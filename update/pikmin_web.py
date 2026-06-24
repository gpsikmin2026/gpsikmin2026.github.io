#!/usr/bin/env python3
"""
GPsikmin Web UI
執行：python3 pikmin_web.py
"""
VERSION = "1.5.0"

import asyncio
import hashlib
import json
import math
import os
import queue
import random
import signal
import socket
import pathlib
import subprocess
import sys
import threading
import time

from datetime import datetime

import requests
from flask import Flask, Response, jsonify, request, send_file
from cryptography.fernet import Fernet, InvalidToken

_ROUTE_KEY = Fernet(b"7_HitDvxbwD5nZPlKdg-P3leGShTTSTYkzCGYMuwyYg=")

# ── 硬體綁定 ─────────────────────────────────────────────
_LOCK_FILE = "/data/.gpsikmin_lock"
_SETUP_DONE_FILE = os.path.expanduser("~/.gpsikmin_setup_done")

def _get_phone_udid():
    # ideviceinfo queries the live connection — returns the ACTUAL connected device's UDID.
    # idevicepair list only reads the pairing DB and may return stale/wrong UDIDs when
    # multiple phones were ever paired.
    try:
        r = subprocess.run(["ideviceinfo", "-k", "UniqueDeviceID"],
                           capture_output=True, text=True, timeout=5)
        udid = r.stdout.strip()
        if udid and r.returncode == 0:
            return udid
    except Exception:
        pass
    return None

def _get_usbmux_udid():
    try:
        r = subprocess.run([PMD3, "usbmux", "list"],
                           capture_output=True, text=True, timeout=5)
        if r.returncode != 0 or not r.stdout.strip():
            return None
        data = json.loads(r.stdout)
        for dev in (data if isinstance(data, list) else []):
            props = dev.get("Properties", dev) if isinstance(dev, dict) else {}
            for key in ("UniqueDeviceID", "SerialNumber", "UDID"):
                val = str(props.get(key, "")).strip()
                if len(val) >= 20:
                    return val
    except Exception:
        pass
    return None

def _is_setup_done(udid):
    try:
        data = json.loads(pathlib.Path(_SETUP_DONE_FILE).read_text())
        return udid in data.get("udids", [])
    except Exception:
        return False

def _mark_setup_done(udid):
    try:
        try:
            data = json.loads(pathlib.Path(_SETUP_DONE_FILE).read_text())
        except Exception:
            data = {"udids": []}
        if udid not in data["udids"]:
            data["udids"].append(udid)
        pathlib.Path(_SETUP_DONE_FILE).write_text(json.dumps(data))
    except Exception:
        pass

def _hw_serial():
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("Serial"):
                    return line.split(":")[1].strip()
    except Exception:
        pass
    return None

def _check_hardware():
    serial = _hw_serial()
    if not serial:
        print("硬體驗證失敗：無法讀取序號")
        sys.exit(1)
    h = hashlib.sha256((serial + "GPsikmin").encode()).hexdigest()
    if not os.path.exists(_LOCK_FILE):
        with open(_LOCK_FILE, "w") as f:
            f.write(h)
        os.chmod(_LOCK_FILE, 0o400)
    else:
        try:
            with open(_LOCK_FILE) as f:
                if f.read().strip() != h:
                    raise ValueError
        except Exception:
            print("硬體驗證失敗：授權不符")
            sys.exit(1)

_check_hardware()
# ─────────────────────────────────────────────────────────

app = Flask(__name__, static_folder="static")

TUNNELD_URL = "http://127.0.0.1:49151"
UPDATE_URL = "https://gpsikmin2026.github.io/update/version.json"
_SELF_PATH = os.path.abspath(__file__)
ROUTES_DIR = os.path.join(os.path.dirname(_SELF_PATH), "routes")
MARKERS_FILE = os.path.join(os.path.dirname(_SELF_PATH), "static", "markers.json")
os.makedirs(ROUTES_DIR, exist_ok=True)

state = {
    "running": False, "lat": None, "lng": None, "progress": 0.0,
    "status": "idle", "speed": 5.0, "eta_min": 0,
    "walked_m": 0.0, "remaining_min": 0.0, "total_dist_m": 0.0,
    "joystick_dir": "stop",
    "last_joystick_ms": 0,
    "joystick_mode": "coarse",
    "joystick_step_m": 100,
}
stop_flag = threading.Event()
goldpot_flag = threading.Event()
gps_thread = None
tunneld_proc = None
_tunneld_starting = False
event_queue: queue.Queue = queue.Queue()

# ── 步數追蹤 ──
_steps_lock = threading.Lock()
_steps_walked_m = 0.0          # 累計已走公尺（未領取）
_steps_last_walked_m = 0.0     # 上次 state["walked_m"] 快照
STEPS_PER_KM = 1300            # 每公里換算步數
STEPS_MAX_PER_CLAIM = 5000     # 每次領取上限
STEPS_DAILY_MAX = 50000        # 每日寫入上限
_steps_today_claimed = 0       # 今日已領取步數
_steps_today_date = ""         # 今日日期（YYYY-MM-DD）

def _add_walked(meters):
    global _steps_walked_m
    state["walked_m"] += meters
    with _steps_lock:
        _steps_walked_m += meters


def _drain_event_queue():
    """清空 event_queue，避免殘留 stopped 事件讓新 SSE 連線誤判結束。"""
    while not event_queue.empty():
        try:
            event_queue.get_nowait()
        except queue.Empty:
            break


LOC_SET_TIMEOUT = 5.0

async def _safe_loc_set(loc, lat, lng):
    try:
        await asyncio.wait_for(loc.set(lat, lng), timeout=LOC_SET_TIMEOUT)
        return True
    except (asyncio.TimeoutError, Exception):
        return False

async def _safe_cleanup(loc, dvt, rsd, skip_clear=False):
    if not skip_clear:
        try:
            await asyncio.wait_for(loc.clear(), timeout=3.0)
        except Exception:
            pass
    try:
        await asyncio.wait_for(dvt.__aexit__(None, None, None), timeout=3.0)
    except Exception:
        pass
    try:
        await asyncio.wait_for(rsd.close(), timeout=3.0)
    except Exception:
        pass


async def _goldpot_countdown(loc):
    """3-2-1 倒數後送 loc.clear()，讓 isSimulatedBySoftware 瞬間清除。回傳是否正常完成。"""
    DRIFT_MAX = 4e-5
    DRIFT_STEP = 6e-6
    lat, lng = state["lat"], state["lng"]
    drift_lat = drift_lng = 0.0
    for c in range(3, 0, -1):
        if stop_flag.is_set():
            return False
        drift_lat = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lat + random.gauss(0, DRIFT_STEP)))
        drift_lng = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lng + random.gauss(0, DRIFT_STEP)))
        if not await _safe_loc_set(loc, lat + drift_lat, lng + drift_lng):
            if stop_flag.is_set():
                return False
        event_queue.put({"goldpot_countdown": c, "lat": lat, "lng": lng})
        await asyncio.sleep(1)
    try:
        await asyncio.wait_for(loc.clear(), timeout=3.0)
    except Exception:
        pass
    event_queue.put({"goldpot_go": True})
    return True


def haversine(lat1, lng1, lat2, lng2) -> float:
    R = 6371000
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a = math.sin(math.radians(lat2 - lat1) / 2) ** 2 + \
        math.cos(p1) * math.cos(p2) * math.sin(math.radians(lng2 - lng1) / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def get_rsd():
    data = requests.get(TUNNELD_URL, timeout=3).json()
    if not data:
        raise RuntimeError("tunneld 沒有偵測到 iPhone")
    udid = list(data.keys())[0]
    t = data[udid][0]
    return t["tunnel-address"], t["tunnel-port"]


async def _simulate(route, speed_kmh, loop_mode):
    from pymobiledevice3.remote.remote_service_discovery import RemoteServiceDiscoveryService
    from pymobiledevice3.services.dvt.instruments.dvt_provider import DvtProvider
    from pymobiledevice3.services.dvt.instruments.location_simulation import LocationSimulation

    rsd_addr, rsd_port = get_rsd()
    rsd = RemoteServiceDiscoveryService((rsd_addr, rsd_port))
    await rsd.connect()
    dvt = DvtProvider(rsd)
    await dvt.__aenter__()
    loc = LocationSimulation(dvt)
    await loc.connect()

    base_speed_mps = speed_kmh / 3.6
    total_dist = sum(haversine(*route[i], *route[i + 1]) for i in range(len(route) - 1))
    total_steps = max(1, total_dist / base_speed_mps)
    state["eta_min"] = total_dist / base_speed_mps / 60
    state["total_dist_m"] = total_dist
    state["walked_m"] = 0.0

    direction, idx, step_count, lap_count = 1, 0, 0, 0
    DRIFT_MAX = 4e-5
    DRIFT_STEP = 6e-6
    drift_lat = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)
    drift_lng = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)
    # 隨機停頓：每 40~120 步觸發一次（模擬看手機、等紅燈）
    steps_until_pause = random.randint(40, 120)

    clear_called = False
    try:
        while not stop_flag.is_set():
            step = direction
            while not stop_flag.is_set() and (
                (direction == 1 and idx < len(route) - 1) or
                (direction == -1 and idx > 0)
            ):
                lat1, lng1 = route[idx]
                lat2, lng2 = route[idx + step]
                seg_dist = haversine(lat1, lng1, lat2, lng2)
                seg_steps = max(1, int(seg_dist / base_speed_mps))
                step_dist_m = seg_dist / seg_steps

                for s in range(seg_steps):
                    if stop_flag.is_set():
                        break
                    if goldpot_flag.is_set():
                        goldpot_flag.clear()
                        clear_called = await _goldpot_countdown(loc)
                        stop_flag.set()
                        break
                    t = s / seg_steps
                    lat = lat1 + (lat2 - lat1) * t
                    lng = lng1 + (lng2 - lng1) * t
                    drift_lat = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lat + random.gauss(0, DRIFT_STEP)))
                    drift_lng = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lng + random.gauss(0, DRIFT_STEP)))
                    if not await _safe_loc_set(loc, lat + drift_lat, lng + drift_lng):
                        if stop_flag.is_set():
                            break
                        continue
                    step_count += 1
                    _add_walked(step_dist_m)
                    pct = min(100.0, step_count / total_steps * 100)
                    remaining_min = max(0.0, total_dist - state["walked_m"]) / base_speed_mps / 60
                    state.update({"lat": lat, "lng": lng, "progress": pct, "remaining_min": remaining_min})
                    event_queue.put({"lat": lat, "lng": lng, "progress": pct,
                                     "walked_m": state["walked_m"], "remaining_min": remaining_min})
                    # 速度抖動 ±15%，加 sleep jitter ±100ms
                    step_speed = max(3.0, min(25.0, speed_kmh * random.uniform(0.85, 1.15)))
                    sleep_t = base_speed_mps / (step_speed / 3.6) + random.uniform(-0.1, 0.15)
                    await asyncio.sleep(max(0.1, sleep_t))
                    # 隨機停頓
                    steps_until_pause -= 1
                    if steps_until_pause <= 0 and not stop_flag.is_set():
                        await asyncio.sleep(random.uniform(3.0, 25.0))
                        steps_until_pause = random.randint(40, 120)
                idx += step

            if stop_flag.is_set():
                break
            state["progress"] = 100.0
            event_queue.put({"lat": route[-1 if direction == 1 else 0][0],
                              "lng": route[-1 if direction == 1 else 0][1],
                              "progress": 100.0, "walked_m": state["walked_m"],
                              "remaining_min": 0.0, "arrived": True})
            if loop_mode:
                lap_count += 1
                direction = -direction
                step_count = 0
                dist_km = state["walked_m"] / 1000
                state["loop_lap"] = lap_count
                event_queue.put({"loop_lap": lap_count, "walked_km": round(dist_km, 2)})
            else:
                break
    finally:
        state["running"] = False
        state["status"] = "idle"
        event_queue.put({"stopped": True})
        await _safe_cleanup(loc, dvt, rsd, skip_clear=clear_called)


def _gps_worker(route, speed_kmh, loop_mode):
    asyncio.run(_simulate(route, speed_kmh, loop_mode))


async def _joystick_simulate():
    from pymobiledevice3.remote.remote_service_discovery import RemoteServiceDiscoveryService
    from pymobiledevice3.services.dvt.instruments.dvt_provider import DvtProvider
    from pymobiledevice3.services.dvt.instruments.location_simulation import LocationSimulation

    rsd_addr, rsd_port = get_rsd()
    rsd = RemoteServiceDiscoveryService((rsd_addr, rsd_port))
    await rsd.connect()
    dvt = DvtProvider(rsd)
    await dvt.__aenter__()
    loc = LocationSimulation(dvt)
    await loc.connect()

    INTERVAL = 0.1
    DRIFT_MAX = 4e-5
    DRIFT_STEP = 6e-6
    drift_lat, drift_lng = 0.0, 0.0
    _remap = {"up": "right", "down": "left", "left": "up", "right": "down", "stop": "stop"}
    prev_dir = "stop"

    try:
        while not stop_flag.is_set():
            _raw = state.get("joystick_dir", "stop")
            d = _remap.get(_raw, "stop")
            mode = state.get("joystick_mode", "coarse")
            lat = state["lat"]
            lng = state["lng"]

            if mode == "coarse":
                if d != "stop" and prev_dir == "stop" and lat is not None:
                    step = state.get("joystick_step_m", 100)
                    cos_lat = math.cos(math.radians(lat))
                    if d == "up":    lat += step / 111000
                    elif d == "down":  lat -= step / 111000
                    elif d == "right": lng += step / (111000 * cos_lat)
                    elif d == "left":  lng -= step / (111000 * cos_lat)
                    state["lat"] = lat
                    state["lng"] = lng
                    _add_walked(step)
                    event_queue.put({"lat": lat, "lng": lng, "progress": 0.0,
                                     "walked_m": state["walked_m"], "remaining_min": 0.0})
                    await _safe_loc_set(loc, lat, lng)
                await asyncio.sleep(0.05)
            else:
                if d != "stop" and lat is not None:
                    speed_mps = state["speed"] / 3.6
                    cos_lat = math.cos(math.radians(lat))
                    if d == "up":    lat += speed_mps * INTERVAL / 111000
                    elif d == "down":  lat -= speed_mps * INTERVAL / 111000
                    elif d == "right": lng += speed_mps * INTERVAL / (111000 * cos_lat)
                    elif d == "left":  lng -= speed_mps * INTERVAL / (111000 * cos_lat)
                    drift_lat = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lat + random.gauss(0, DRIFT_STEP)))
                    drift_lng = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lng + random.gauss(0, DRIFT_STEP)))
                    state["lat"] = lat
                    state["lng"] = lng
                    _add_walked(speed_mps * INTERVAL)
                    event_queue.put({"lat": lat, "lng": lng, "progress": 0.0,
                                     "walked_m": state["walked_m"], "remaining_min": 0.0})
                    await _safe_loc_set(loc, lat + drift_lat, lng + drift_lng)
                await asyncio.sleep(INTERVAL)

            prev_dir = d
    finally:
        state["running"] = False
        state["status"] = "idle"
        state["joystick_dir"] = "stop"
        event_queue.put({"stopped": True})
        await _safe_cleanup(loc, dvt, rsd)


def _joystick_thread_worker():
    asyncio.run(_joystick_simulate())


@app.route("/")
def index():
    return HTML_PAGE


@app.route("/route", methods=["POST"])
def calc_route():
    pts = request.json.get("waypoints", [])
    if len(pts) < 2:
        return jsonify({"error": "至少需要 2 個點"}), 400
    coords_str = ";".join(f"{p['lng']},{p['lat']}" for p in pts)
    resp = requests.get(f"http://router.project-osrm.org/route/v1/foot/{coords_str}",
                        params={"overview": "full", "geometries": "geojson"}, timeout=15)
    data = resp.json()
    if data.get("code") != "Ok":
        return jsonify({"error": "路線規劃失敗"}), 500
    route_coords = data["routes"][0]["geometry"]["coordinates"]
    return jsonify({
        "coords": [{"lat": c[1], "lng": c[0]} for c in route_coords],
        "dist_km": round(data["routes"][0]["distance"] / 1000, 2),
        "dur_min": round(data["routes"][0]["duration"] / 60, 0),
    })


@app.route("/start", methods=["POST"])
def start():
    global gps_thread
    if state["running"]:
        return jsonify({"error": "已在執行中"}), 400
    body = request.json
    route_pts = body.get("route", [])
    speed_kmh = float(body.get("speed", 5.0))
    loop_mode = bool(body.get("loop", False))
    if len(route_pts) < 2:
        return jsonify({"error": "路線點數不足"}), 400
    try:
        get_rsd()
    except Exception as e:
        return jsonify({"error": f"tunneld 未啟動：{e}"}), 500
    route = [(p["lat"], p["lng"]) for p in route_pts]
    _drain_event_queue()
    stop_flag.clear()
    state.update({"running": True, "status": "running", "speed": speed_kmh,
                  "lat": route[0][0], "lng": route[0][1], "progress": 0.0, "walked_m": 0.0})
    gps_thread = threading.Thread(target=_gps_worker, args=(route, speed_kmh, loop_mode), daemon=True)
    gps_thread.start()
    return jsonify({"ok": True})


@app.route("/start_patrol", methods=["POST"])
def start_patrol():
    global gps_thread
    if state["running"]:
        return jsonify({"error": "已在執行中"}), 400
    body = request.json
    waypoints = body.get("waypoints", [])
    dwell_sec = max(30, int(float(body.get("dwell_minutes", 5)) * 60))
    patrol_loop = bool(body.get("patrol_loop", False))
    if len(waypoints) < 1:
        return jsonify({"error": "請至少設定一個中繼點"}), 400
    try:
        get_rsd()
    except Exception as e:
        return jsonify({"error": f"tunneld 未啟動：{e}"}), 500
    pts = [(p["lat"], p["lng"]) for p in waypoints]
    _drain_event_queue()
    stop_flag.clear()
    state.update({"running": True, "status": "patrol", "lat": pts[0][0], "lng": pts[0][1],
                  "progress": 0.0, "walked_m": 0.0, "patrol_idx": 0, "patrol_total": len(pts),
                  "patrol_remaining": dwell_sec, "patrol_loop": patrol_loop})
    gps_thread = threading.Thread(target=_patrol_worker, args=(pts, dwell_sec, patrol_loop), daemon=True)
    gps_thread.start()
    return jsonify({"ok": True})


async def _patrol_simulate(waypoints, dwell_sec, patrol_loop=False):
    from pymobiledevice3.remote.remote_service_discovery import RemoteServiceDiscoveryService
    from pymobiledevice3.services.dvt.instruments.dvt_provider import DvtProvider
    from pymobiledevice3.services.dvt.instruments.location_simulation import LocationSimulation
    rsd_addr, rsd_port = get_rsd()
    rsd = RemoteServiceDiscoveryService((rsd_addr, rsd_port))
    await rsd.connect()
    dvt = DvtProvider(rsd)
    await dvt.__aenter__()
    loc = LocationSimulation(dvt)
    await loc.connect()

    DRIFT_MAX = 4e-5
    DRIFT_STEP = 6e-6

    clear_called = False
    try:
        lap = 0
        while not stop_flag.is_set():
            lap += 1
            for idx, (lat, lng) in enumerate(waypoints):
                if stop_flag.is_set():
                    break
                drift_lat = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)
                drift_lng = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)
                elapsed = 0
                state.update({"patrol_idx": idx + 1, "lat": lat, "lng": lng, "patrol_lap": lap})
                while elapsed < dwell_sec and not stop_flag.is_set():
                    if goldpot_flag.is_set():
                        goldpot_flag.clear()
                        clear_called = await _goldpot_countdown(loc)
                        stop_flag.set()
                        break
                    drift_lat = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lat + random.gauss(0, DRIFT_STEP)))
                    drift_lng = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lng + random.gauss(0, DRIFT_STEP)))
                    if not await _safe_loc_set(loc, lat + drift_lat, lng + drift_lng):
                        if stop_flag.is_set():
                            break
                    remaining = dwell_sec - elapsed
                    progress = ((idx + elapsed / dwell_sec) / len(waypoints)) * 100
                    dwell_pct = (elapsed / dwell_sec) * 100
                    state.update({"progress": progress, "patrol_remaining": remaining, "dwell_pct": dwell_pct})
                    event_queue.put({"lat": lat, "lng": lng, "progress": progress,
                                     "dwell_pct": dwell_pct,
                                     "patrol_idx": idx + 1, "patrol_total": len(waypoints),
                                     "patrol_remaining": remaining, "patrol_lap": lap,
                                     "patrol_loop": patrol_loop})
                    sleep_t = 2.0 + random.uniform(-0.2, 0.3)
                    await asyncio.sleep(sleep_t)
                    elapsed += sleep_t

            if stop_flag.is_set():
                break
            if not patrol_loop:
                event_queue.put({"patrol_done": True, "progress": 100.0,
                                 "patrol_idx": len(waypoints), "patrol_total": len(waypoints),
                                 "patrol_remaining": 0})
                break
            # 循環：重新開始，通知前端換圈
            event_queue.put({"patrol_lap_done": True, "patrol_lap": lap,
                             "patrol_total": len(waypoints)})
    finally:
        state["running"] = False
        state["status"] = "idle"
        event_queue.put({"stopped": True})
        await _safe_cleanup(loc, dvt, rsd, skip_clear=clear_called)


def _patrol_worker(waypoints, dwell_sec, patrol_loop=False):
    asyncio.run(_patrol_simulate(waypoints, dwell_sec, patrol_loop))


@app.route("/start_flower", methods=["POST"])
def start_flower():
    global gps_thread
    if state["running"]:
        return jsonify({"error": "已在執行中"}), 400
    body = request.json
    try:
        center_lat = float(body.get("lat"))
        center_lng = float(body.get("lng"))
    except (TypeError, ValueError):
        return jsonify({"error": "座標格式錯誤"}), 400
    dwell_sec = float(body.get("dwell_sec", 3))
    try:
        get_rsd()
    except Exception as e:
        return jsonify({"error": f"tunneld 未啟動：{e}"}), 500
    _drain_event_queue()
    stop_flag.clear()
    state.update({"running": True, "status": "flower", "lat": center_lat, "lng": center_lng,
                  "progress": 0.0, "walked_m": 0.0})
    gps_thread = threading.Thread(target=_flower_worker,
                                  args=(center_lat, center_lng, dwell_sec), daemon=True)
    gps_thread.start()
    return jsonify({"ok": True})


async def _flower_simulate(center_lat, center_lng, dwell_sec):
    from pymobiledevice3.remote.remote_service_discovery import RemoteServiceDiscoveryService
    from pymobiledevice3.services.dvt.instruments.dvt_provider import DvtProvider
    from pymobiledevice3.services.dvt.instruments.location_simulation import LocationSimulation

    rsd_addr, rsd_port = get_rsd()
    rsd = RemoteServiceDiscoveryService((rsd_addr, rsd_port))
    await rsd.connect()
    dvt = DvtProvider(rsd)
    await dvt.__aenter__()
    loc = LocationSimulation(dvt)
    await loc.connect()

    # pt2 = 使用者選的定位點；pt1 = 自動在 5m 外隨機方向產生
    OFFSET_M = 5
    SPEED_KMH = 4.0
    speed_mps = SPEED_KMH / 3.6          # 1.11 m/s
    interval = 0.5                        # 每 0.5 秒送一次座標
    steps = max(4, int(OFFSET_M / speed_mps / interval))  # 每段步數

    bearing_rad = random.uniform(0, 2 * math.pi)
    d_lat = OFFSET_M / 111320
    d_lng = OFFSET_M / (111320 * math.cos(math.radians(center_lat)))
    pt1 = (center_lat + d_lat * math.cos(bearing_rad),
           center_lng + d_lng * math.sin(bearing_rad))
    pt2 = (center_lat, center_lng)

    try:
        # Phase 1：pt1 → pt2 單程移動，讓遊戲偵測到座標變化
        for s in range(steps + 1):
            if stop_flag.is_set():
                break
            t = s / steps
            lat = pt1[0] + (pt2[0] - pt1[0]) * t
            lng = pt1[1] + (pt2[1] - pt1[1]) * t
            if not await _safe_loc_set(loc, lat, lng):
                if stop_flag.is_set():
                    break
                continue
            state.update({"lat": lat, "lng": lng})
            event_queue.put({"lat": lat, "lng": lng})
            await asyncio.sleep(interval + random.uniform(-0.05, 0.1))

        # Phase 2：停在 pt2，加小漂移避免遊戲認為定位凍結
        while not stop_flag.is_set():
            dlat = random.gauss(0, 4e-6)
            dlng = random.gauss(0, 4e-6)
            if not await _safe_loc_set(loc, pt2[0] + dlat, pt2[1] + dlng):
                if stop_flag.is_set():
                    break
                continue
            state.update({"lat": pt2[0] + dlat, "lng": pt2[1] + dlng})
            event_queue.put({"lat": pt2[0] + dlat, "lng": pt2[1] + dlng})
            await asyncio.sleep(0.5 + random.uniform(-0.05, 0.1))
    finally:
        state["running"] = False
        state["status"] = "idle"
        event_queue.put({"stopped": True})
        await _safe_cleanup(loc, dvt, rsd)


def _flower_worker(center_lat, center_lng, dwell_sec):
    asyncio.run(_flower_simulate(center_lat, center_lng, dwell_sec))


@app.route("/start_circle", methods=["POST"])
def start_circle():
    global gps_thread
    if state["running"]:
        return jsonify({"error": "已在執行中"}), 400
    body = request.json
    try:
        center_lat = float(body.get("lat"))
        center_lng = float(body.get("lng"))
    except (TypeError, ValueError):
        return jsonify({"error": "座標格式錯誤"}), 400
    radius_m = float(body.get("radius_m", 20))
    speed_kmh = float(body.get("speed_kmh", 4))
    try:
        get_rsd()
    except Exception as e:
        return jsonify({"error": f"tunneld 未啟動：{e}"}), 500
    _drain_event_queue()
    stop_flag.clear()
    state.update({"running": True, "status": "circle", "lat": center_lat, "lng": center_lng,
                  "progress": 0.0, "walked_m": 0.0})
    gps_thread = threading.Thread(target=_circle_worker,
                                  args=(center_lat, center_lng, radius_m, speed_kmh), daemon=True)
    gps_thread.start()
    return jsonify({"ok": True})


async def _circle_simulate(center_lat, center_lng, radius_m, speed_kmh):
    from pymobiledevice3.remote.remote_service_discovery import RemoteServiceDiscoveryService
    from pymobiledevice3.services.dvt.instruments.dvt_provider import DvtProvider
    from pymobiledevice3.services.dvt.instruments.location_simulation import LocationSimulation

    rsd_addr, rsd_port = get_rsd()
    rsd = RemoteServiceDiscoveryService((rsd_addr, rsd_port))
    await rsd.connect()
    dvt = DvtProvider(rsd)
    await dvt.__aenter__()
    loc = LocationSimulation(dvt)
    await loc.connect()

    speed_mps = speed_kmh / 3.6
    interval = 1.0
    angular_step = (speed_mps * interval) / radius_m
    d_lat = radius_m / 111320
    d_lng = radius_m / (111320 * math.cos(math.radians(center_lat)))
    angle = 0.0
    DRIFT_MAX = 4e-5
    DRIFT_STEP = 6e-6
    drift_lat = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)
    drift_lng = random.uniform(-DRIFT_MAX/2, DRIFT_MAX/2)

    try:
        while not stop_flag.is_set():
            lat = center_lat + d_lat * math.cos(angle)
            lng = center_lng + d_lng * math.sin(angle)
            drift_lat = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lat + random.gauss(0, DRIFT_STEP)))
            drift_lng = max(-DRIFT_MAX, min(DRIFT_MAX, drift_lng + random.gauss(0, DRIFT_STEP)))
            if not await _safe_loc_set(loc, lat + drift_lat, lng + drift_lng):
                if stop_flag.is_set():
                    break
                continue
            state.update({"lat": lat, "lng": lng})
            event_queue.put({"lat": lat, "lng": lng})
            angle = (angle + angular_step) % (2 * math.pi)
            await asyncio.sleep(interval + random.uniform(-0.1, 0.15))
    finally:
        state["running"] = False
        state["status"] = "idle"
        event_queue.put({"stopped": True})
        await _safe_cleanup(loc, dvt, rsd)


def _circle_worker(center_lat, center_lng, radius_m, speed_kmh):
    asyncio.run(_circle_simulate(center_lat, center_lng, radius_m, speed_kmh))


@app.route("/start_goldpot", methods=["POST"])
def start_goldpot():
    if not state["running"]:
        return jsonify({"error": "需要在模擬執行中才能使用"}), 400
    goldpot_flag.set()
    return jsonify({"ok": True})


@app.route("/stop", methods=["POST"])
def stop():
    stop_flag.set()
    state["status"] = "stopping"
    def _force_stop():
        time.sleep(10)
        if state["running"]:
            state["running"] = False
            state["status"] = "idle"
            event_queue.put({"stopped": True})
    threading.Thread(target=_force_stop, daemon=True).start()
    return jsonify({"ok": True})


# ── 步數 API ──────────────────────────────────────────────
def _steps_reset_if_new_day():
    global _steps_today_claimed, _steps_today_date
    today = time.strftime("%Y-%m-%d")
    if _steps_today_date != today:
        _steps_today_claimed = 0
        _steps_today_date = today

@app.route("/api/steps", methods=["GET"])
def api_steps():
    global _steps_walked_m, _steps_today_claimed
    with _steps_lock:
        _steps_reset_if_new_day()
        avail = int(_steps_walked_m / 1000 * STEPS_PER_KM)
        daily_room = max(0, STEPS_DAILY_MAX - _steps_today_claimed)
        give = min(avail, STEPS_MAX_PER_CLAIM, daily_room)
        if give > 0:
            consumed_m = give / STEPS_PER_KM * 1000
            _steps_walked_m = max(0, _steps_walked_m - consumed_m)
            _steps_today_claimed += give
    return Response(str(give), mimetype="text/plain")


@app.route("/api/steps/peek", methods=["GET"])
def api_steps_peek():
    with _steps_lock:
        _steps_reset_if_new_day()
        avail = int(_steps_walked_m / 1000 * STEPS_PER_KM)
        daily_room = max(0, STEPS_DAILY_MAX - _steps_today_claimed)
    return jsonify({"steps": avail, "today_claimed": _steps_today_claimed,
                     "daily_room": daily_room, "daily_max": STEPS_DAILY_MAX})


# ── OTA 更新 ──────────────────────────────────────────────
def _is_overlayroot():
    return os.path.isdir("/media/root-ro") and os.path.ismount("/media/root-ro")

@app.route("/api/update/check")
def api_update_check():
    try:
        r = requests.get(UPDATE_URL, timeout=10)
        r.raise_for_status()
        info = r.json()
        remote_ver = info.get("version", "0")
        return jsonify({"current": VERSION, "latest": remote_ver,
                         "changelog": info.get("changelog", ""),
                         "has_update": remote_ver != VERSION})
    except Exception as e:
        return jsonify({"error": f"無法連線更新伺服器：{e}"}), 502

@app.route("/api/update/apply", methods=["POST"])
def api_update_apply():
    if state["running"]:
        return jsonify({"error": "模擬執行中，請先停止再更新"}), 400
    try:
        r = requests.get(UPDATE_URL, timeout=10)
        r.raise_for_status()
        info = r.json()
        if info.get("version") == VERSION:
            return jsonify({"error": "已是最新版本"}), 400
        file_url = info.get("url")
        expected_sha256 = info.get("sha256", "")
        if not file_url:
            return jsonify({"error": "更新資訊缺少下載連結"}), 500

        fr = requests.get(file_url, timeout=30)
        fr.raise_for_status()
        new_code = fr.content

        if expected_sha256:
            actual = hashlib.sha256(new_code).hexdigest()
            if actual != expected_sha256:
                return jsonify({"error": f"檔案驗證失敗（hash 不符）"}), 500

        if _is_overlayroot():
            real_path = _SELF_PATH.replace("/home/", "/media/root-ro/home/", 1)
            overlay_path = _SELF_PATH.replace("/home/", "/media/root-rw/overlay/home/", 1)
            subprocess.run(["sudo", "bash", "-c", "mount -o remount,rw /media/root-ro"], check=True, timeout=10)
            os.makedirs(os.path.dirname(real_path), exist_ok=True)
            with open(real_path, "wb") as f:
                f.write(new_code)
            subprocess.run(["sudo", "bash", "-c", "mount -o remount,ro /media/root-ro"], check=True, timeout=10)
            os.makedirs(os.path.dirname(overlay_path), exist_ok=True)
            with open(overlay_path, "wb") as f:
                f.write(new_code)
        else:
            backup = _SELF_PATH + f".bak_{time.strftime('%Y%m%d_%H%M%S')}"
            os.rename(_SELF_PATH, backup)
            with open(_SELF_PATH, "wb") as f:
                f.write(new_code)

        threading.Thread(target=_delayed_restart, daemon=True).start()
        return jsonify({"ok": True, "new_version": info["version"],
                         "message": "更新完成，3 秒後自動重啟..."})
    except subprocess.CalledProcessError as e:
        return jsonify({"error": f"寫入失敗：{e}"}), 500
    except Exception as e:
        return jsonify({"error": f"更新失敗：{e}"}), 500

def _delayed_restart():
    time.sleep(3)
    for svc in ("gpsikmin", "GPsikmin"):
        r = subprocess.run(["systemctl", "is-active", svc], capture_output=True, text=True)
        if r.stdout.strip() == "active":
            subprocess.run(["sudo", "systemctl", "restart", svc], timeout=10)
            return

@app.route("/api/version")
def api_version():
    return jsonify({"version": VERSION})


@app.route("/api/joystick/mode", methods=["POST"])
def api_joystick_mode():
    body = request.json or {}
    m = body.get("mode", "coarse")
    if m not in ("coarse", "fine"):
        return jsonify({"error": "mode 必須是 coarse 或 fine"}), 400
    state["joystick_mode"] = m
    if "step_m" in body:
        s = int(body["step_m"])
        if s in (50, 100, 200, 500):
            state["joystick_step_m"] = s
    return jsonify({"ok": True, "mode": m, "step_m": state["joystick_step_m"]})


@app.route("/api/joystick", methods=["POST"])
def api_joystick():
    global gps_thread
    body = request.json or {}
    d = body.get("dir", "stop")
    if d not in ("up", "down", "left", "right", "stop"):
        return jsonify({"error": f"無效方向：{d}"}), 400

    if "lat" in body and "lng" in body:
        state["lat"] = float(body["lat"])
        state["lng"] = float(body["lng"])
    if "speed" in body:
        state["speed"] = float(body["speed"])

    state["joystick_dir"] = d
    state["last_joystick_ms"] = int(time.time() * 1000)

    has_coords = "lat" in body and "lng" in body
    if not state["running"] and (d != "stop" or has_coords):
        if state["lat"] is None or state["lng"] is None:
            return jsonify({"error": "請先提供起始座標 lat/lng"}), 400
        try:
            get_rsd()
        except Exception as e:
            return jsonify({"error": f"tunneld 未啟動：{e}"}), 500
        _drain_event_queue()
        stop_flag.clear()
        state.update({"running": True, "status": "joystick",
                      "progress": 0.0, "walked_m": 0.0})
        gps_thread = threading.Thread(target=_joystick_thread_worker, daemon=True)
        gps_thread.start()

    return jsonify({"ok": True, "dir": d})


@app.route("/status")
def status():
    return jsonify(state)


@app.route("/stream")
def stream():
    def generate():
        while True:
            try:
                evt = event_queue.get(timeout=30)
                yield f"data: {json.dumps(evt)}\n\n"
                if evt.get("stopped"):
                    time.sleep(0.3)
                    break
            except queue.Empty:
                yield "data: {\"ping\":true}\n\n"
    return Response(generate(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


@app.route("/save_route", methods=["POST"])
def save_route():
    body = request.json
    name = body.get("name", "").strip()
    if not name:
        return jsonify({"error": "請輸入路線名稱"}), 400
    waypoints = body.get("waypoints", [])
    if len(waypoints) < 2:
        return jsonify({"error": "路線至少需要 2 個中繼點"}), 400
    safe_name = "".join(c for c in name if c.isalnum() or c in "-_()[]，。！ ").strip()
    filename = f"{safe_name}_{datetime.now().strftime('%m%d%H%M')}.json"
    with open(os.path.join(ROUTES_DIR, filename), "w", encoding="utf-8") as f:
        json.dump({"name": name, "waypoints": waypoints,
                   "route_coords": body.get("route_coords", []),
                   "dist_km": body.get("dist_km", 0),
                   "created": datetime.now().isoformat()}, f, ensure_ascii=False, indent=2)
    return jsonify({"ok": True, "filename": filename})


@app.route("/list_routes")
def list_routes():
    routes = []
    for fn in sorted(os.listdir(ROUTES_DIR), reverse=True):
        if not fn.endswith(".json"):
            continue
        try:
            with open(os.path.join(ROUTES_DIR, fn), encoding="utf-8") as f:
                d = json.load(f)
            routes.append({"filename": fn, "name": d.get("name", fn),
                            "dist_km": d.get("dist_km", 0),
                            "created": d.get("created", "")[:16].replace("T", " ")})
        except Exception:
            pass
    return jsonify(routes)


@app.route("/load_route/<path:filename>")
def load_route(filename):
    filepath = os.path.join(ROUTES_DIR, os.path.basename(filename))
    if not os.path.exists(filepath):
        return jsonify({"error": "找不到路線"}), 404
    with open(filepath, encoding="utf-8") as f:
        return jsonify(json.load(f))


@app.route("/delete_route/<path:filename>", methods=["DELETE"])
def delete_route(filename):
    filepath = os.path.join(ROUTES_DIR, os.path.basename(filename))
    if os.path.exists(filepath):
        os.remove(filepath)
    return jsonify({"ok": True})


@app.route("/export_route/<path:filename>")
def export_route(filename):
    filepath = os.path.join(ROUTES_DIR, os.path.basename(filename))
    if not os.path.exists(filepath):
        return jsonify({"error": "找不到路線"}), 404
    with open(filepath, "rb") as f:
        encrypted = _ROUTE_KEY.encrypt(f.read())
    import io
    buf = io.BytesIO(encrypted)
    dl_name = os.path.splitext(os.path.basename(filename))[0] + ".gpsikmin"
    return send_file(buf, as_attachment=True, download_name=dl_name,
                     mimetype="application/octet-stream")


@app.route("/api/import_route", methods=["POST"])
def api_import_route():
    f = request.files.get("file")
    if not f:
        return jsonify({"error": "沒有收到檔案"}), 400
    raw = f.read()
    if f.filename.endswith(".gpsikmin"):
        try:
            raw = _ROUTE_KEY.decrypt(raw)
        except InvalidToken:
            return jsonify({"error": "檔案無效或非本裝置授權"}), 403
    try:
        data = json.loads(raw)
        assert "waypoints" in data
    except Exception:
        return jsonify({"error": "路線格式錯誤"}), 400
    stem = os.path.splitext(os.path.basename(f.filename))[0]
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out = os.path.join(ROUTES_DIR, f"{stem}_{ts}.json")
    with open(out, "w", encoding="utf-8") as fp:
        json.dump(data, fp, ensure_ascii=False)
    return jsonify({"ok": True, "saved": os.path.basename(out)})


@app.route("/api/markers", methods=["GET"])
def get_markers():
    if os.path.exists(MARKERS_FILE):
        with open(MARKERS_FILE, encoding="utf-8") as f:
            return jsonify(json.load(f))
    return jsonify([])

@app.route("/api/markers", methods=["POST"])
def save_markers():
    data = request.get_json(force=True)
    with open(MARKERS_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    return jsonify({"ok": True})


UPLOAD_DIR = "/tmp/gpsikmin_uploads"

@app.route("/api/map_image", methods=["POST"])
def api_map_image():
    if "file" not in request.files:
        return jsonify({"error": "no file"}), 400
    f = request.files["file"]
    try:
        os.makedirs(UPLOAD_DIR, exist_ok=True)
        filename = f"overlay_{int(time.time())}.jpg"
        filepath = os.path.join(UPLOAD_DIR, filename)
        with open(filepath, "wb") as out:
            out.write(f.read())
        return jsonify({"url": f"/api/overlay_img/{filename}"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/overlay_img/<filename>")
def api_overlay_img(filename):
    from flask import send_from_directory
    return send_from_directory(UPLOAD_DIR, filename)


@app.route("/geocode")
def geocode():
    q = request.args.get("q", "").strip()
    if not q:
        return jsonify({"error": "請輸入搜尋內容"}), 400
    try:
        resp = requests.get("https://nominatim.openstreetmap.org/search",
                            params={"q": q, "format": "json", "limit": 5, "accept-language": "zh-TW,zh"},
                            headers={"User-Agent": "GPsikmin/1.0"}, timeout=10)
        return jsonify([{"name": r.get("display_name", ""),
                         "lat": float(r["lat"]), "lng": float(r["lon"])} for r in resp.json()])
    except Exception as e:
        return jsonify({"error": str(e)}), 500


def _get_ios_major_version():
    try:
        r = subprocess.run(["ideviceinfo", "-k", "ProductVersion"],
                           capture_output=True, text=True, timeout=5)
        ver = r.stdout.strip()
        if ver:
            return int(ver.split(".")[0])
    except Exception:
        pass
    return None

@app.route("/api/setup/state")
def api_setup_state():
    udid = _get_phone_udid()
    if udid:
        ios_ver = _get_ios_major_version()
        if ios_ver is not None and ios_ver < 17:
            return jsonify({"step": -1, "status": "ios_too_old",
                            "message": f"您的 iOS {ios_ver} 不支援，請升級至 iOS 17 或以上版本"})
        try:
            r = subprocess.run([PMD3, "amfi", "developer-mode-status"],
                               capture_output=True, text=True, timeout=8)
            if r.stdout.strip().lower() == "false":
                return jsonify({"step": 2, "status": "needs_devmode"})
        except Exception:
            pass
        if not _is_setup_done(udid):
            _mark_setup_done(udid)
        return jsonify({"step": 4, "status": "ready"})

    usbmux_udid = _get_usbmux_udid()
    if usbmux_udid and _is_setup_done(usbmux_udid):
        return jsonify({"step": 4, "status": "ready"})

    r = subprocess.run(["idevicepair", "pair"], capture_output=True, text=True, timeout=5)
    out = r.stdout + r.stderr
    if "trust dialog" in out.lower():
        return jsonify({"step": 1, "status": "needs_trust"})
    if "SUCCESS" in out:
        udid = usbmux_udid
        if udid and _is_setup_done(udid):
            return jsonify({"step": 4, "status": "ready"})
        return jsonify({"step": 2, "status": "needs_devmode"})
    if usbmux_udid:
        return jsonify({"step": 0, "status": "phone_locked",
                        "message": "手機已偵測到，請解鎖手機螢幕後再點「偵測手機」"})
    return jsonify({"step": 0, "status": "no_phone"})


@app.route("/api/setup/detect_phone", methods=["POST"])
def api_setup_detect_phone():
    subprocess.run(["sudo", "systemctl", "restart", "usbmuxd-persistent"],
                   capture_output=True, timeout=10)
    time.sleep(3)
    r = subprocess.run(["idevicepair", "pair"], capture_output=True, text=True, timeout=6)
    out = r.stdout + r.stderr
    if "trust dialog" in out.lower():
        return jsonify({"step": 1, "status": "needs_trust"})
    if "SUCCESS" in out or "already" in out.lower():
        return jsonify({"step": 2, "status": "needs_devmode"})
    if "No device found" in out:
        return jsonify({"step": 0, "status": "no_phone"})
    return jsonify({"step": 0, "status": "no_phone", "detail": out.strip()})


@app.route("/api/setup/pair", methods=["POST"])
def api_setup_pair():
    r = subprocess.run(["idevicepair", "pair"], capture_output=True, text=True, timeout=5)
    out = r.stdout + r.stderr
    if "trust dialog" in out.lower():
        return jsonify({"ok": False, "needs_trust": True})
    ok = "SUCCESS" in out or "already" in out.lower()
    return jsonify({"ok": ok, "output": out.strip()})


@app.route("/api/setup/reveal_devmode", methods=["POST"])
def api_setup_reveal_devmode():
    r = subprocess.run([PMD3, "amfi", "reveal-developer-mode"], capture_output=True, text=True, timeout=10)
    return jsonify({"ok": True, "output": (r.stdout + r.stderr).strip()})


@app.route("/api/setup/wait_reboot")
def api_setup_wait_reboot():
    def generate():
        # Phase 1: wait for disconnect — use ideviceinfo which tests live connection
        for _ in range(30):
            r = subprocess.run(["ideviceinfo"], capture_output=True, text=True, timeout=5)
            if r.returncode != 0:
                break
            time.sleep(2)
        yield 'data: {"status":"disconnected"}\n\n'
        # Phase 2: wait for reconnect and unlock — pair succeeds when accessible
        for _ in range(60):
            time.sleep(2)
            try:
                r = subprocess.run(["idevicepair", "pair"], capture_output=True, text=True, timeout=5)
                out = r.stdout + r.stderr
                if "SUCCESS" in out or "already" in out.lower():
                    yield 'data: {"status":"reconnected"}\n\n'
                    return
            except Exception:
                pass
        yield 'data: {"status":"timeout"}\n\n'
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


@app.route("/api/setup/mount", methods=["POST"])
def api_setup_mount():
    fix_dns()
    try:
        r = subprocess.run([PMD3, "mounter", "auto-mount"], capture_output=True, text=True, timeout=120)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 or "successfully" in out.lower() or "already mounted" in out.lower()
        if ok:
            udid = _get_phone_udid()
            if not udid:
                # ideviceinfo may not be ready yet right after reboot; fall back to DB
                try:
                    r2 = subprocess.run(["idevicepair", "list"], capture_output=True, text=True, timeout=5)
                    lines = [l.strip() for l in r2.stdout.strip().splitlines() if l.strip()]
                    udid = lines[0] if lines else None
                except Exception:
                    pass
            if udid:
                _mark_setup_done(udid)
        return jsonify({"ok": ok, "output": out.strip()})
    except subprocess.TimeoutExpired:
        return jsonify({"ok": False, "output": "安裝超時（120秒），請確認網路正常後重試"})
    except Exception as e:
        return jsonify({"ok": False, "output": str(e)})


@app.route("/connect_phone", methods=["POST"])
def connect_phone():
    global tunneld_proc, _tunneld_starting
    if _tunneld_starting:
        return jsonify({"ok": False, "message": "正在連線中，請稍候…"})
    if tunneld_proc and tunneld_proc.poll() is None:
        try:
            r = requests.get(TUNNELD_URL, timeout=2)
            if r.json():
                return jsonify({"ok": True, "message": "iPhone 已連線，可以開始模擬"})
        except Exception:
            pass
    if not check_iphone():
        return jsonify({"ok": False, "message": "找不到 iPhone，請確認 USB 已接好並信任此電腦"})
    fix_dns()
    tunneld_proc = ensure_tunneld()
    try:
        r = requests.get(TUNNELD_URL, timeout=3)
        if r.json():
            return jsonify({"ok": True, "message": "iPhone 已連線，可以開始模擬"})
    except Exception:
        pass
    return jsonify({"ok": False, "message": "tunneld 啟動失敗，請重試"})


@app.route("/phone_status")
def phone_status():
    try:
        r = requests.get(TUNNELD_URL, timeout=2)
        connected = bool(r.json())
    except Exception:
        connected = False
    return jsonify({"connected": connected})


HTML_PAGE = r"""<!DOCTYPE html>
<html lang="zh-TW">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>🌱 GPsikmin</title>
<link rel="stylesheet" href="/static/leaflet.css"/>
<script src="/static/leaflet.js"></script>
<style>
* { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: -apple-system, sans-serif; background: #1a1a2e; color: #eee; height: 100vh; display: flex; flex-direction: row; overflow: hidden; }

#map { flex: 1; min-width: 0; }

#sidebar { width: 280px; flex-shrink: 0; display: flex; flex-direction: column; background: #16213e; border-left: 2px solid #2a2a4e; overflow-y: auto; }
#btn-sb-toggle { display: none; }

#header { background: #16213e; padding: 7px 10px; display: flex; align-items: center; gap: 5px; flex-wrap: wrap; border-bottom: 1px solid #2a2a4e; }
#header h1 { font-size: 0.75rem; color: #7ee8a2; white-space: nowrap; width: 100%; }
.ctrl { display: flex; align-items: center; gap: 5px; font-size: 0.62rem; }
.ctrl label { color: #aaa; white-space: nowrap; }
input[type=range] { width: 80px; accent-color: #7ee8a2; }
#speed-val { color: #7ee8a2; font-weight: bold; min-width: 42px; }
input[type=checkbox] { accent-color: #7ee8a2; width: 15px; height: 15px; }
.btn { padding: 3px 7px; border: none; border-radius: 6px; cursor: pointer; font-size: 0.62rem; font-weight: bold; white-space: nowrap; touch-action: manipulation; }
#btn-start { background: #7ee8a2; color: #1a1a2e; }
#btn-start:disabled { background: #555; color: #888; cursor: not-allowed; }
#btn-stop     { background: #e87e7e; color: #1a1a2e; }
#btn-goldpot  { background: #7a5a00; color: #ffe; }
#btn-undo     { background: #4a4a6a; color: #ccc; }
#btn-clear { background: #4a4a6a; color: #ccc; }
#btn-afk.afk-on { background: #7b5ea7; color: #fff; }
#action-btns { display: flex; flex-wrap: wrap; gap: 5px; }
.marker-type-row { display:flex; gap:4px; width:100%; }
.btn-mtype { flex:1; background:#4a4a6a; color:#ccc; border:none; border-radius:6px; padding:4px 2px; font-size:1rem; cursor:pointer; border:2px solid transparent; transition:border-color 0.1s; }
.btn-mtype.active { border-color:#f59e0b; background:#5a4a2a; }

/* 搜尋框 */
.search-wrap { position: relative; display: flex; align-items: center; gap: 4px; width: 100%; }
#search-input { background: #2a2a4e; border: 1px solid #3a3a6e; color: #eee; border-radius: 5px; padding: 3px 6px; font-size: 0.62rem; flex: 1; min-width: 0; }
#search-input::placeholder { color: #555; }
#btn-search { background: #5b8dee; color: #fff; border: none; border-radius: 5px; padding: 3px 7px; cursor: pointer; font-size: 0.62rem; font-weight: bold; flex-shrink: 0; }
#search-results { position: absolute; top: calc(100% + 4px); left: 0; right: 0; background: #1e2a4e; border: 1px solid #3a3a6e; border-radius: 6px; z-index: 9999; max-height: 210px; overflow-y: auto; display: none; box-shadow: 0 4px 12px #000a; }
#search-results div { padding: 5px 9px; cursor: pointer; font-size: 0.62rem; border-bottom: 1px solid #2a2a4e; line-height: 1.3; }
#search-results div:hover { background: #2a3a6e; }
#search-results div:last-child { border-bottom: none; }

/* 可折疊面板 */
.panel-wrap { border-bottom: 1px solid #2a2a4e; }
.panel-toggle { width: 100%; background: none; border: none; color: #7ee8a2; font-size: 0.62rem; font-weight: bold; cursor: pointer; padding: 4px 12px; display: flex; align-items: center; gap: 6px; }
.panel-toggle:hover { background: rgba(255,255,255,0.03); }
.panel-inner { padding: 0 16px 8px; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
.panel-inner.collapsed { display: none; }
#route-bar { background: #111830; }
.rl { color: #888; font-size: 0.62rem; white-space: nowrap; }
#route-name { background: #2a2a4e; border: 1px solid #3a3a6e; color: #eee; border-radius: 5px; padding: 3px 6px; font-size: 0.62rem; width: 115px; }
#route-select { background: #2a2a4e; border: 1px solid #3a3a6e; color: #eee; border-radius: 5px; padding: 3px 5px; font-size: 0.62rem; flex: 1; min-width: 140px; max-width: 270px; }
.btn-sm { padding: 3px 7px; border: none; border-radius: 5px; cursor: pointer; font-size: 0.62rem; font-weight: bold; white-space: nowrap; }
#btn-save { background: #5b8dee; color: #fff; }
#btn-save:disabled { background: #555; color: #888; cursor: not-allowed; }
#btn-load { background: #7ee8a2; color: #1a1a2e; }
#btn-load:disabled { background: #555; color: #888; cursor: not-allowed; }
#btn-del  { background: #4a4a6a; color: #ccc; }
.btn-gpx  { background: #a855f7; color: #fff; cursor: pointer; }
.btn-gpx input { display: none; }
input[type=time] { background: #2a2a4e; border: 1px solid #3a3a6e; color: #eee; border-radius: 5px; padding: 2px 4px; font-size: 0.62rem; }

/* 資訊列 */
#info-bar { position: fixed; top: 10px; right: 300px; max-width: 260px; background: rgba(15,52,96,0.88); backdrop-filter: blur(4px); border: 1px solid #2a4a7e; border-radius: 8px; padding: 5px 10px; font-size: 0.58rem; color: #aef; display: flex; flex-direction: column; gap: 3px; z-index: 500; pointer-events: none; }
#info-row { display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }
#progress-bar { width: 100%; height: 6px; background: #333; border-radius: 3px; }
#progress-fill { height: 100%; background: #7ee8a2; border-radius: 3px; width: 0%; transition: width 0.5s; }
.stat { color: #7ee8a2; font-weight: bold; white-space: nowrap; }
.wp-label { background: #e87e7e; color: #fff; border-radius: 50%; width: 24px; height: 24px; display: flex; align-items: center; justify-content: center; font-size: 12px; font-weight: bold; }

/* 熱點篩選按鈕 */
.sf-btn { background:#2a2a4e;color:#aaa;border:1px solid #3a3a6e;border-radius:4px;padding:3px 7px;cursor:pointer;font-size:0.62rem; }
.sf-btn:hover { background:#3a3a6e; }
.sf-btn.sf-active { background:#5b8dee;color:#fff;border-color:#5b8dee; }

/* Leaflet popup 深色主題 */
.leaflet-popup-content-wrapper { background: #1e2a4e !important; color: #eee !important; border: 1px solid #3a3a6e !important; box-shadow: 0 4px 12px #000a !important; }
.leaflet-popup-tip { background: #1e2a4e !important; }
.leaflet-popup-close-button { color: #aaa !important; }

/* GPS 十字標記 */
.goto-cross { position: relative; width: 32px; height: 32px; cursor: pointer; }
.goto-cross::before, .goto-cross::after { content:''; position: absolute; background: #ff4444; border-radius: 2px; }
.goto-cross::before { width: 3px; height: 100%; left: 50%; transform: translateX(-50%); }
.goto-cross::after  { width: 100%; height: 3px; top: 50%; transform: translateY(-50%); }
.goto-cross-ring { position: absolute; top: 50%; left: 50%; width: 14px; height: 14px; border: 2px solid #ff4444; border-radius: 50%; transform: translate(-50%,-50%); }

/* 地圖智取 */
#overlay-opacity { width: 100%; accent-color: #7ee8a2; cursor: pointer; margin: 2px 0; }
.overlay-active { background: #7ee8a2 !important; color: #16213e !important; font-weight: bold; }
.overlay-corner { width: 26px; height: 26px; background: #7ee8a2; border: 2px solid #fff; border-radius: 50%; cursor: move; }

/* GPS 座標跳轉框 */
#goto-box { position: fixed; bottom: 24px; left: 10px; background: rgba(15,52,96,0.92); backdrop-filter: blur(4px); border: 1px solid #2a4a7e; border-radius: 8px; padding: 6px 8px; z-index: 500; display: flex; gap: 5px; align-items: center; }
#goto-box input { background: #0d1b3e; border: 1px solid #3a3a6e; border-radius: 5px; color: #eee; padding: 4px 7px; font-size: 0.65rem; width: 155px; outline: none; }
#goto-box input::placeholder { color: #556; }
#goto-box button { background: #5b8dee; border: none; border-radius: 5px; color: #fff; padding: 4px 8px; font-size: 0.65rem; cursor: pointer; white-space: nowrap; }
#goto-box button:hover { background: #7aaaf5; }

/* 行動版：改回上下排列 */
@media (max-width: 768px) {
  body { flex-direction: column; }
  #sidebar { width: 100%; border-left: none; border-top: 2px solid #2a2a4e; max-height: 52vh; transition: max-height 0.25s ease; }
  #sidebar.sb-collapsed { max-height: 44px !important; overflow: hidden; }
  #btn-sb-toggle { display: inline-block; }
  #map { flex: 1; min-height: 0; }
  #info-bar { right: 10px; top: 10px; font-size: 0.72rem; }
  #goto-box { left: 8px; }

  /* 放大觸控按鈕 */
  button { touch-action: manipulation; -webkit-tap-highlight-color: transparent; }
  .btn { font-size: 0.9rem !important; padding: 10px 14px !important; }
  .btn-sm { font-size: 0.88rem !important; padding: 9px 12px !important; }
  .btn-mtype { font-size: 1.3rem !important; padding: 10px 4px !important; }

  /* 控制列字體 */
  .ctrl { font-size: 0.82rem !important; gap: 8px; }
  .ctrl label { font-size: 0.82rem !important; }
  input[type=checkbox] { width: 22px !important; height: 22px !important; cursor: pointer; }
  input[type=range] { width: 110px !important; }
  #speed-val { font-size: 0.84rem !important; }

  /* 標題列 */
  #header { padding: 10px 12px; gap: 9px; }
  #header h1 { font-size: 0.95rem; }

  /* 操作按鈕 2 欄 Grid */
  #action-btns { display: grid !important; grid-template-columns: 1fr 1fr; gap: 8px; width: 100%; }
  #action-btns .marker-type-row { grid-column: 1 / -1; }
  #btn-start, #btn-stop { grid-column: 1 / -1; }

  /* 尋菇/瞬移/繞圈展開面板 */
  #mushroom-dwell-row *, #flower-settings *, #circle-settings * { font-size: 0.82rem !important; }
  #mushroom-dwell-row input, #flower-settings input, #circle-settings input { padding: 6px 8px !important; }
  #mushroom-dwell-row button, #flower-settings button, #circle-settings button { padding: 9px 10px !important; }

  /* 搜尋框 */
  #search-input { font-size: 0.84rem !important; padding: 9px 10px !important; }
  #btn-search { font-size: 0.84rem !important; padding: 9px 12px !important; }

  /* 可折疊面板 */
  .panel-toggle { font-size: 0.88rem; padding: 10px 14px; }
  .panel-inner { padding: 8px 14px 12px; gap: 9px; }
  .rl { font-size: 0.84rem !important; }
  #route-name { font-size: 0.84rem !important; padding: 8px 8px !important; }
  #route-select { font-size: 0.84rem !important; padding: 8px 8px !important; }
  input[type=time] { font-size: 0.84rem !important; padding: 8px 6px !important; }
  .sf-btn { font-size: 0.84rem !important; padding: 9px 12px !important; }

  /* GPS 跳轉框 */
  #goto-box input { font-size: 0.84rem !important; padding: 8px 10px !important; width: 140px !important; }
  #goto-box button { font-size: 0.84rem !important; padding: 8px 10px !important; }
}
#setup-overlay {
  display: none; position: fixed; inset: 0; background: rgba(0,0,0,.7);
  z-index: 9999; align-items: center; justify-content: center;
}
#setup-overlay.active { display: flex; }
#setup-box {
  background: #1e1e3a; border: 1px solid #4a4a8a; border-radius: 12px;
  padding: 24px; width: 340px; max-width: 95vw; color: #eee;
}
#setup-box h3 { font-size: 1.1rem; margin-bottom: 16px; text-align: center; }
.setup-step {
  display: flex; align-items: flex-start; gap: 10px;
  padding: 8px; border-radius: 6px; margin-bottom: 6px; font-size: 0.85rem;
}
.setup-step.active { background: #2a2a5a; }
.setup-step.done { opacity: .5; }
.step-icon { font-size: 1.1rem; width: 22px; flex-shrink: 0; text-align: center; }
.step-text { flex: 1; }
.step-title { font-weight: bold; margin-bottom: 2px; }
.step-desc { color: #aaa; font-size: 0.78rem; }
#setup-msg {
  background: #2a2a4e; border-radius: 8px; padding: 12px;
  margin: 14px 0; font-size: 0.82rem; line-height: 1.5; min-height: 48px;
}
#setup-progress-bar {
  height: 4px; background: #4a4a6a; border-radius: 2px; margin-bottom: 14px; overflow: hidden;
}
#setup-progress-fill { height: 100%; background: #7ee8a2; width: 0; transition: width .4s; }
#setup-action-btn {
  width: 100%; padding: 10px; background: #5a5aaa; color: #fff;
  border: none; border-radius: 8px; font-size: 0.9rem; cursor: pointer;
}
#setup-action-btn:disabled { background: #3a3a6a; color: #888; cursor: default; }
#setup-action-btn.success { background: #4a9a6a; }

/* ── 說明手冊 Modal ── */
#help-overlay { display:none; position:fixed; inset:0; background:rgba(0,0,0,.78); z-index:9998; align-items:center; justify-content:center; }
#help-overlay.active { display:flex; }
#help-box { background:#1a1a30; border:1px solid #4a4a8a; border-radius:12px; width:92vw; max-width:540px; max-height:88vh; display:flex; flex-direction:column; color:#eee; box-shadow:0 8px 32px #000c; }
#help-hdr { display:flex; justify-content:space-between; align-items:center; padding:13px 18px; border-bottom:1px solid #2a2a5a; flex-shrink:0; }
#help-hdr span { font-size:1rem; font-weight:bold; color:#7ee8a2; }
#help-hdr button { background:none; border:none; color:#aaa; font-size:1.3rem; cursor:pointer; line-height:1; padding:2px 6px; }
#help-body { overflow-y:auto; padding:6px 0 12px; }
.hs { border-bottom:1px solid #222244; }
.hs-btn { width:100%; background:none; border:none; color:#aef; font-size:0.85rem; font-weight:bold; padding:11px 18px; text-align:left; cursor:pointer; display:flex; justify-content:space-between; align-items:center; touch-action:manipulation; }
.hs-btn:hover { background:rgba(255,255,255,.04); }
.hs-body { display:none; padding:2px 18px 12px; font-size:0.8rem; line-height:1.7; color:#bbb; }
.hs-body.open { display:block; }
.hs-body b { color:#7ee8a2; }
.hs-body .tip { background:#1e2a4e; border-left:3px solid #5b8dee; border-radius:4px; padding:6px 10px; margin:6px 0; font-size:0.78rem; color:#9bd; }
.hs-body ul { padding-left:1.2em; margin:4px 0; }
.hs-body li { margin-bottom:3px; }
.hs-body table { width:100%; border-collapse:collapse; margin:6px 0; font-size:0.78rem; }
.hs-body td { padding:4px 8px; border:1px solid #2a2a5a; }
.hs-body tr:first-child td { background:#1e2a4e; color:#aef; font-weight:bold; }
</style>
</head>
<body>

<div id="map"></div>

<div id="goto-box">
  <input type="text" id="goto-input" placeholder="緯度,經度 (e.g. 25.05,121.53)"
         onkeydown="if(event.key==='Enter')gotoCoord()">
  <button onclick="gotoCoord()">➤ 跳轉</button>
</div>

<div id="sidebar">
  <div id="header">
    <div style="display:flex;align-items:center;justify-content:space-between;width:100%">
      <h1 style="width:auto">🌱 GPsikmin <span id="ver-tag" style="font-size:0.45rem;color:#666;font-weight:normal"></span></h1>
      <div style="display:flex;gap:5px">
        <button id="btn-sb-toggle" onclick="toggleSidebar()" style="background:#2a4a2a;border:1px solid #3a6a3a;color:#7ee8a2;border-radius:6px;padding:4px 10px;font-size:0.68rem;cursor:pointer;touch-action:manipulation;white-space:nowrap">⬇ 收起</button>
        <button onclick="openHelp()" style="background:#2a3a6a;border:1px solid #3a4a8a;color:#aef;border-radius:6px;padding:4px 10px;font-size:0.68rem;cursor:pointer;touch-action:manipulation;white-space:nowrap">❓ 說明</button>
      </div>
    </div>
    <div class="ctrl">
      <label>速度</label>
      <input type="range" id="speed" min="3" max="25" step="0.5" value="5">
      <span id="speed-val">5.0 km/h</span>
    </div>
    <div class="ctrl"><input type="checkbox" id="loop"><label for="loop">折返</label></div>
    <div class="ctrl"><input type="checkbox" id="straight"><label for="straight">直線</label></div>
    <div class="ctrl">
      <input type="checkbox" id="mushroom-mode" onchange="onMushroomModeChange()">
      <label for="mushroom-mode">🍄 尋菇模式</label>
    </div>
    <div id="mushroom-dwell-row" style="display:none;flex-direction:column;gap:4px;padding:2px 0">
      <div style="display:flex;align-items:center;gap:4px;font-size:0.62rem;color:#ccc">
        <label>停留</label>
        <input type="number" id="dwell-minutes" value="5" min="1" max="30"
               style="width:38px;background:#2a2a4e;border:1px solid #3a3a6e;color:#eee;border-radius:4px;padding:2px 4px;font-size:0.62rem;text-align:center">
        <label>分鐘/點</label>
        <input type="checkbox" id="patrol-loop" style="margin-left:6px">
        <label for="patrol-loop">循環</label>
      </div>
      <button class="btn" onclick="openPickMarkersModal()"
              style="background:#5a3a8a;color:#ddd;width:100%" title="從已存標記挑選尋菇點">
        📌 從標記選點
      </button>
    </div>
    <div class="ctrl">
      <input type="checkbox" id="flower-mode" onchange="onFlowerModeChange()">
      <label for="flower-mode">🌸 瞬間移動</label>
    </div>
    <div id="flower-settings" style="display:none;flex-direction:column;gap:5px;padding:2px 0">
      <div style="display:flex;align-items:center;gap:4px;font-size:0.62rem;color:#ccc">
        <input type="text" id="flower-coord" placeholder="緯度,經度"
               onkeydown="if(event.key==='Enter')flowerConfirmCoord()"
               style="flex:1;background:#2a2a4e;border:1px solid #3a3a6e;color:#eee;border-radius:4px;padding:3px 5px;font-size:0.62rem;outline:none">
        <button onclick="flowerUseMapCenter()" title="使用地圖中心"
                style="background:#5b8dee;border:none;border-radius:4px;color:#fff;padding:3px 6px;font-size:0.62rem;cursor:pointer;white-space:nowrap">📍 地圖中心</button>
      </div>
      <button onclick="flowerConfirmCoord()"
              style="background:#4a7a5a;border:none;border-radius:5px;color:#eee;padding:4px;font-size:0.65rem;cursor:pointer;width:100%">
        ✓ 確認座標（在地圖上標記）
      </button>
      <div id="flower-confirmed" style="display:none;font-size:0.6rem;color:#7ee8a2;padding:1px 0">
        ✅ 已設定目標點
      </div>
      <div style="display:flex;align-items:center;gap:4px;font-size:0.62rem;color:#ccc">
        <label style="color:#888">先移到目標 5m 外，再移過去並停留</label>
      </div>
    </div>
    <div class="ctrl">
      <input type="checkbox" id="circle-mode" onchange="onCircleModeChange()">
      <label for="circle-mode">🚶 繞圈種花</label>
    </div>
    <div id="circle-settings" style="display:none;flex-direction:column;gap:5px;padding:2px 0">
      <div style="display:flex;align-items:center;gap:4px;font-size:0.62rem;color:#ccc">
        <input type="text" id="circle-coord" placeholder="緯度,經度"
               onkeydown="if(event.key==='Enter')circleConfirmCoord()"
               style="flex:1;background:#2a2a4e;border:1px solid #3a3a6e;color:#eee;border-radius:4px;padding:3px 5px;font-size:0.62rem;outline:none">
        <button onclick="circleUseMapCenter()" title="使用地圖中心"
                style="background:#5b8dee;border:none;border-radius:4px;color:#fff;padding:3px 6px;font-size:0.62rem;cursor:pointer;white-space:nowrap">📍 地圖中心</button>
      </div>
      <button onclick="circleConfirmCoord()"
              style="background:#4a7a5a;border:none;border-radius:5px;color:#eee;padding:4px;font-size:0.65rem;cursor:pointer;width:100%">
        ✓ 確認座標（在地圖上標記）
      </button>
      <div id="circle-confirmed" style="display:none;font-size:0.6rem;color:#7ee8a2;padding:1px 0">
        ✅ 已設定目標點
      </div>
      <div style="display:flex;align-items:center;gap:4px;font-size:0.62rem;color:#ccc">
        <label>半徑</label>
        <input type="range" id="circle-radius" min="10" max="50" step="5" value="20"
               oninput="document.getElementById('circle-radius-val').textContent=this.value+'m'"
               style="flex:1">
        <span id="circle-radius-val">20m</span>
      </div>
    </div>
    <div class="ctrl"><input type="checkbox" id="auto-follow" checked><label for="auto-follow">跟隨</label></div>
    <div id="action-btns">
      <button class="btn" id="btn-undo"  onclick="undoWaypoint()">↩ 上一點</button>
      <button class="btn" id="btn-clear" onclick="clearAll()">🗑 清除</button>
      <div class="marker-type-row" title="選擇標記類型後點地圖新增">
        <button class="btn-mtype" id="mtype-mushroom" onclick="toggleMarkerMode('mushroom')" title="蘑菇">🍄</button>
        <button class="btn-mtype" id="mtype-plant"    onclick="toggleMarkerMode('plant')"    title="大花">🌸</button>
        <button class="btn-mtype" id="mtype-special"  onclick="toggleMarkerMode('special')"  title="明信片">⭐</button>
        <button class="btn-mtype" id="mtype-pin"      onclick="toggleMarkerMode('pin')"      title="標記">📍</button>
      </div>
      <button class="btn" onclick="openMarkersModal()"
              style="background:#3a5a8a;color:#ccc" title="我的標記清單">📋 我的標記</button>
      <button class="btn" id="btn-connect" onclick="connectPhone()" style="background:#4a4a6a;color:#ccc" title="連線 iPhone">🔌 連線手機</button>
      <button class="btn" id="btn-afk" onclick="toggleAfkMode()" style="background:#4a4a6a;color:#ccc" title="掛機：斷線自動重連並重啟">🌙 掛機模式</button>
      <button class="btn" id="btn-start"   onclick="startSim()" disabled>▶ 開始</button>
      <button class="btn" id="btn-stop"    onclick="stopSim()" style="display:none">⏹ 停止</button>
      <button class="btn" id="btn-goldpot" onclick="startGoldpot()" style="display:none" title="凍結GPS在金盆位置，倒數後斷線DVT，趁機互動金盆（需配合 IPLocate）">🪣 拉金盆</button>
      <button class="btn" id="btn-joystick" onclick="toggleJoystick()" style="background:#4a4a6a;color:#ccc" title="實體搖桿模式">🕹️ 搖桿 <span id="ble-dot" style="color:#555" title="搖桿未連線">●</span></button>
      <div style="display:flex;gap:4px;margin-top:4px">
        <button id="btn-mode-coarse" onclick="setJoyMode('coarse')"
          style="flex:1;padding:3px;border:none;border-radius:4px;font-size:0.72rem;cursor:pointer;background:#7c6cd4;color:#fff">粗調</button>
        <button id="btn-mode-fine" onclick="setJoyMode('fine')"
          style="flex:1;padding:3px;border:none;border-radius:4px;font-size:0.72rem;cursor:pointer;background:#444;color:#aaa">微調</button>
      </div>
      <div id="coarse-steps" style="display:flex;gap:3px;margin-top:3px">
        <span style="font-size:0.65rem;color:#888;align-self:center">跳距：</span>
        <button onclick="setJoyStep(50)"  id="btn-step-50"  style="flex:1;padding:2px;border:none;border-radius:4px;font-size:0.68rem;cursor:pointer;background:#444;color:#aaa">50m</button>
        <button onclick="setJoyStep(100)" id="btn-step-100" style="flex:1;padding:2px;border:none;border-radius:4px;font-size:0.68rem;cursor:pointer;background:#7c6cd4;color:#fff">100m</button>
        <button onclick="setJoyStep(200)" id="btn-step-200" style="flex:1;padding:2px;border:none;border-radius:4px;font-size:0.68rem;cursor:pointer;background:#444;color:#aaa">200m</button>
        <button onclick="setJoyStep(500)" id="btn-step-500" style="flex:1;padding:2px;border:none;border-radius:4px;font-size:0.68rem;cursor:pointer;background:#444;color:#aaa">500m</button>
      </div>
    </div>
    <div class="search-wrap">
      <input type="text" id="search-input" placeholder="🔍 搜尋地點"
             onkeydown="if(event.key==='Enter')searchPlace()">
      <button id="btn-search" onclick="searchPlace()">搜尋</button>
      <div id="search-results"></div>
    </div>
  </div>

  <div id="overlay-panel" class="panel-wrap">
    <button class="panel-toggle" onclick="togglePanel('overlay-content','overlay-arrow')">
      🗾 疊圖輔助 <span id="overlay-arrow">▸</span>
    </button>
    <div id="overlay-content" class="panel-inner collapsed">
      <div style="font-size:0.62rem;color:#888;margin-bottom:4px">先把地圖移到截圖對應的區域，再上傳</div>
      <label class="btn-sm" style="background:#4a6a7a;color:#eee;cursor:pointer;text-align:center;width:100%">
        📸 上傳遊戲截圖
        <input type="file" id="overlay-file" accept="image/*" style="display:none" onchange="uploadMapImage(event)">
      </label>
      <div id="overlay-controls" style="display:none;width:100%">
        <div style="display:flex;gap:4px;flex-wrap:wrap;margin-top:4px">
          <button id="btn-overlay-pick" class="btn-sm" onclick="toggleOverlayPickMode()" style="flex:1">🎯 定位取點</button>
          <button class="btn-sm" onclick="removeMapOverlay()" style="background:#6a2a2a;color:#eee">🗑 移除</button>
        </div>
        <div style="display:flex;align-items:center;gap:6px;margin-top:5px">
          <span style="font-size:0.63rem;color:#888;white-space:nowrap">透明度</span>
          <input type="range" id="overlay-opacity" min="10" max="100" value="70" oninput="setOverlayOpacity(this.value)">
        </div>
        <div style="font-size:0.62rem;color:#666;margin-top:4px">🟡 底部平移　🟢 角點縮放　🔴 右側旋轉</div>
        <input type="hidden" id="overlay-rotation" value="0">
        <input type="hidden" id="overlay-scale" value="100">
      </div>
    </div>
  </div>

  <div id="route-bar" class="panel-wrap">
    <button class="panel-toggle" onclick="togglePanel('route-content','route-arrow')">
      📁 路線管理 <span id="route-arrow">▾</span>
    </button>
    <div id="route-content" class="panel-inner">
      <span class="rl">儲存：</span>
      <input type="text" id="route-name" placeholder="路線名稱">
      <button class="btn-sm" id="btn-save" onclick="saveRoute()" disabled>💾 儲存</button>
      <span class="rl" style="margin-left:6px">載入：</span>
      <select id="route-select"><option value="">-- 選擇路線 --</option></select>
      <button class="btn-sm" id="btn-load" onclick="loadRoute()" disabled>📂 載入</button>
      <button class="btn-sm" id="btn-spots" onclick="openSpotsModal()"
              style="background:#e879a0;color:#fff" title="載入 pogoskill 熱點座標">🗺️ 熱點</button>
      <button class="btn-sm" id="btn-del"  onclick="deleteRoute()">🗑</button>
      <button class="btn-sm" id="btn-export" onclick="exportRoute()" disabled title="加密匯出 .gpsikmin">⬇ 匯出</button>
      <button class="btn-sm" style="background:#4a6a7a;color:#eee" onclick="document.getElementById('import-file-input').click()">⬆ 匯入</button>
      <input type="file" id="import-file-input" accept="*/*" style="display:none" onchange="importRoute(event)">
      <label class="btn-sm btn-gpx" title="匯入 GPX">📁 GPX<input type="file" accept=".gpx" onchange="importGPX(event)"></label>
    </div>
  </div>

  <div id="steps-panel" class="panel-wrap">
    <button class="panel-toggle" onclick="togglePanel('steps-content','steps-arrow')">
      👟 自動加步數 <span id="steps-arrow">▸</span>
    </button>
    <div id="steps-content" class="panel-inner collapsed" style="flex-direction:column;align-items:stretch">
      <div style="font-size:0.62rem;color:#888;margin-bottom:4px">模擬行走自動累計步數，iOS 自動化寫入 HealthKit</div>
      <div style="display:flex;align-items:center;gap:8px;margin-bottom:3px">
        <span style="font-size:0.7rem;color:#7ee8a2">待領取：</span>
        <span id="steps-pending" style="font-size:0.9rem;font-weight:bold;color:#fff">0 步</span>
      </div>
      <div style="display:flex;align-items:center;gap:8px;margin-bottom:6px">
        <span style="font-size:0.62rem;color:#aaa">今日已寫入：</span>
        <span id="steps-today" style="font-size:0.75rem;color:#ccc">0</span>
        <span style="font-size:0.62rem;color:#666">/ 50,000 步</span>
      </div>
      <div style="background:#1a2a3a;border-radius:4px;height:6px;margin-bottom:6px;overflow:hidden">
        <div id="steps-daily-bar" style="height:100%;background:#7ee8a2;width:0%;transition:width 0.5s"></div>
      </div>
      <button onclick="copyStepsUrl()" style="background:#3a6aaa;color:#fff;border:none;border-radius:5px;padding:7px;font-size:0.7rem;cursor:pointer;width:100%;margin-bottom:5px">
        📋 複製步數 API 網址
      </button>
      <div id="steps-url-copied" style="display:none;font-size:0.6rem;color:#7ee8a2;text-align:center;margin-bottom:4px">✅ 已複製！</div>
      <div style="font-size:0.55rem;color:#666;margin-bottom:4px">每次最多領 5,000 步，每日上限 50,000 步</div>
      <div style="font-size:0.58rem;color:#999;line-height:1.7">
        <b style="color:#ffd700">⚡ 建立捷徑（只需做一次）：</b><br>
        ① 開啟 iPhone 的<b style="color:#fff">「捷徑」App</b><br>
        ② 右上角點 <b style="color:#7ee8a2">＋</b> 新增捷徑<br>
        ③ 點<b style="color:#7ee8a2">「加入動作」</b>→ 搜尋<b style="color:#fff">「取得URL的內容」</b>→ 點選<br>
        ④ 點網址欄位，輸入 <b style="color:#7ee8a2">http://192.168.4.1:5000/api/steps</b><br>
        ⑤ 點下方 <b style="color:#7ee8a2">＋</b> 再加一個動作 → 搜尋<b style="color:#fff">「紀錄健康樣本」</b>→ 點選<br>
        ⑥ 類型選<b style="color:#fff">「步數」</b>，數值點一下選<b style="color:#fff">「URL 的內容」</b><br>
        ⑦ 改名為<b style="color:#7ee8a2">「加步數」</b>→ 點<b style="color:#7ee8a2">「完成」</b><br>
        <b style="color:#ffd700;margin-top:4px;display:inline-block">⏰ 設定自動執行（建立 4 個自動化）：</b><br>
        ⑧ 切到<b style="color:#fff">「自動化」</b>頁籤 → 右上角 <b style="color:#7ee8a2">＋</b><br>
        ⑨ 選<b style="color:#fff">「每天的特定時間」</b>→ 時間設 <b style="color:#7ee8a2">08:00</b><br>
        ⑩ 動作選<b style="color:#fff">「執行捷徑」</b>→ 選<b style="color:#7ee8a2">「加步數」</b><br>
        ⑪ 關閉<b style="color:#fff">「執行前先詢問」</b>→ 完成 ✅<br>
        ⑫ 重複以上步驟，再建 <b style="color:#7ee8a2">12:00、18:00、22:00</b> 共四個
      </div>
      <div style="font-size:0.55rem;color:#666;margin-top:4px;line-height:1.5">
        ⚠️ 設定 → 健康 → 資料權限 → 捷徑 → 允許寫入「步行」
      </div>
    </div>
  </div>

  <div id="update-panel" class="panel-wrap">
    <button class="panel-toggle" onclick="togglePanel('update-content','update-arrow')">
      🔄 軟體更新 <span id="update-arrow">▸</span>
    </button>
    <div id="update-content" class="panel-inner collapsed" style="flex-direction:column;align-items:stretch">
      <div style="display:flex;align-items:center;gap:8px;margin-bottom:6px">
        <span style="font-size:0.65rem;color:#aaa">目前版本：</span>
        <span id="update-current" style="font-size:0.75rem;color:#7ee8a2;font-weight:bold"></span>
      </div>
      <button id="btn-update-check" onclick="checkUpdate()" style="background:#3a6aaa;color:#fff;border:none;border-radius:5px;padding:7px;font-size:0.7rem;cursor:pointer;width:100%;margin-bottom:5px">
        🔍 檢查更新
      </button>
      <div id="update-result" style="display:none;font-size:0.62rem;color:#ccc;line-height:1.6;margin-bottom:5px;padding:6px;background:#1a2a3a;border-radius:4px"></div>
      <button id="btn-update-apply" onclick="applyUpdate()" style="display:none;background:#e8a040;color:#1a1a2e;border:none;border-radius:5px;padding:7px;font-size:0.7rem;font-weight:bold;cursor:pointer;width:100%">
        ⬆ 立即更新
      </button>
      <div style="font-size:0.52rem;color:#555;margin-top:4px">需要 iPhone USB 連線提供網路</div>
    </div>
  </div>


</div>

<div id="info-bar">
  <span id="info-text">👆 在地圖上點選路線中繼點（至少 2 點）</span>
  <div id="info-row">
    <span class="stat" id="stat-walked" style="display:none"></span>
    <span class="stat" id="stat-eta"    style="display:none"></span>
    <span id="progress-text">0%</span>
  </div>
  <div id="progress-bar"><div id="progress-fill"></div></div>
</div>
<script>
delete L.Icon.Default.prototype._getIconUrl;
L.Icon.Default.mergeOptions({
  iconUrl:'/static/marker-icon.png', iconRetinaUrl:'/static/marker-icon-2x.png', shadowUrl:'/static/marker-shadow.png'
});

const map = L.map('map').setView([25.05, 121.53], 13);
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {attribution:'© OpenStreetMap', maxZoom:19}).addTo(map);

let waypoints=[], wpMarkers=[], routeLayer=null, posMarker=null;
let routeCoords=[], routeDistKm=0, eventSource=null;
let isRunning=false, loadingRoute=false, lastStopPos=null, markerMode=false, customMarkers=[];
let phoneConnected=false;

const MARKER_ICONS = {mushroom:'🍄', plant:'🌸', special:'⭐', pin:'📍'};
const MARKER_NAMES = {mushroom:'蘑菇', plant:'社區植物', special:'特殊地點', pin:'一般'};

function haversineJS(lat1,lng1,lat2,lng2) {
  const R=6371000, dLat=(lat2-lat1)*Math.PI/180, dLng=(lng2-lng1)*Math.PI/180;
  const a=Math.sin(dLat/2)**2+Math.cos(lat1*Math.PI/180)*Math.cos(lat2*Math.PI/180)*Math.sin(dLng/2)**2;
  return R*2*Math.atan2(Math.sqrt(a),Math.sqrt(1-a));
}

// ── 可折疊面板 ──
function togglePanel(contentId, arrowId) {
  const collapsed = document.getElementById(contentId).classList.toggle('collapsed');
  document.getElementById(arrowId).textContent = collapsed ? '▸' : '▾';
}

// ── 地圖點選 ──
map.on('click', e => {
  if (isRunning) return;
  if (markerMode) { showMarkerForm(e.latlng.lat, e.latlng.lng, activeMarkerType); return; }
  if (overlayPickMode) { addWaypoint(e.latlng.lat, e.latlng.lng); return; }
  if (mapImageOverlay) return;
  addWaypoint(e.latlng.lat, e.latlng.lng);
});

// ── 中繼點 ──
function addWaypoint(lat, lng) {
  const n = waypoints.length + 1;
  waypoints.push({lat, lng});
  const icon = L.divIcon({className:'', html:`<div class="wp-label">${n}</div>`, iconSize:[24,24], iconAnchor:[12,12]});
  const marker = L.marker([lat,lng], {icon, draggable:true}).addTo(map);
  marker.on('dragend', function() {
    if (isRunning) return;
    const idx = wpMarkers.indexOf(this);
    if (idx<0) return;
    const pos = this.getLatLng();
    waypoints[idx] = {lat:pos.lat, lng:pos.lng};
    if (!loadingRoute && waypoints.length>=2) fetchRoute();
  });
  wpMarkers.push(marker);
  if (!loadingRoute && waypoints.length>=2) fetchRoute();
  updateUI();
}

function undoWaypoint() {
  if (!waypoints.length) return;
  waypoints.pop(); const m=wpMarkers.pop(); if(m) map.removeLayer(m);
  if (waypoints.length>=2) fetchRoute(); else clearRoute();
  updateUI();
}

function clearAll() {
  waypoints=[]; wpMarkers.forEach(m=>map.removeLayer(m)); wpMarkers=[];
  clearRoute(); updateUI();
  localStorage.removeItem('gpsikmin-route');
}

function clearRoute() {
  if (routeLayer) { map.removeLayer(routeLayer); routeLayer=null; }
  routeCoords=[]; routeDistKm=0;
  document.getElementById('info-text').textContent='👆 在地圖上點選路線中繼點（至少 2 點）';
}

// ── GPS 座標跳轉 ──
function updateGotoBoxPos() {
  if (window.innerWidth <= 768) {
    const h = document.getElementById('sidebar').getBoundingClientRect().height;
    document.getElementById('goto-box').style.bottom = (h + 8) + 'px';
  } else {
    document.getElementById('goto-box').style.bottom = '';
  }
}
new ResizeObserver(updateGotoBoxPos).observe(document.getElementById('sidebar'));
window.addEventListener('resize', updateGotoBoxPos);
updateGotoBoxPos();

let gotoMarker = null;

function flyToSpot(lat, lng, name, type) {
  if (gotoMarker) { map.removeLayer(gotoMarker); gotoMarker = null; }
  map.flyTo([lat, lng], 17, {animate: true, duration: 1.2});
  setTimeout(() => {
    const icon = L.divIcon({
      className: '',
      html: '<div class="goto-cross"><div class="goto-cross-ring"></div></div>',
      iconSize: [32, 32], iconAnchor: [16, 16], popupAnchor: [0, -18]
    });
    gotoMarker = L.marker([lat, lng], {icon}).addTo(map);
    const emoji = type ? (MARKER_ICONS[type] || '📍') : '📍';
    gotoMarker.bindPopup(
      `<div style="text-align:center;font-size:0.75rem">
        <b>${emoji} ${name}</b><br>
        <span style="color:#aaa;font-size:0.65rem">${lat.toFixed(5)}, ${lng.toFixed(5)}</span><br>
        <div style="display:flex;gap:4px;margin-top:6px;justify-content:center">
          <button onclick="addWaypoint(${lat},${lng});map.closePopup()"
            style="padding:3px 8px;background:#5b8dee;border:none;border-radius:4px;color:#fff;cursor:pointer;font-size:0.7rem">
            ➕ 中繼點
          </button>
          <button onclick="map.removeLayer(gotoMarker);gotoMarker=null;map.closePopup()"
            style="padding:3px 8px;background:#555;border:none;border-radius:4px;color:#fff;cursor:pointer;font-size:0.7rem">
            ✕ 移除
          </button>
        </div>
      </div>`
    ).openPopup();
  }, 1300);
}

function gotoCoord() {
  const raw = document.getElementById('goto-input').value.trim();
  const parts = raw.split(/[\s,，]+/);
  if (parts.length < 2) { alert('格式錯誤，請輸入「緯度,經度」例如 25.05,121.53'); return; }
  const lat = parseFloat(parts[0]), lng = parseFloat(parts[1]);
  if (isNaN(lat) || isNaN(lng) || lat < -90 || lat > 90 || lng < -180 || lng > 180) {
    alert('座標超出範圍，請確認緯度(-90~90)與經度(-180~180)'); return;
  }
  if (gotoMarker) { map.removeLayer(gotoMarker); gotoMarker = null; }
  map.flyTo([lat, lng], 17, {animate: true, duration: 1.2});
  setTimeout(() => {
    const icon = L.divIcon({
      className: '',
      html: '<div class="goto-cross"><div class="goto-cross-ring"></div></div>',
      iconSize: [32, 32],
      iconAnchor: [16, 16],
      popupAnchor: [0, -18]
    });
    gotoMarker = L.marker([lat, lng], {icon}).addTo(map);
    gotoMarker.bindPopup(
      `<div style="text-align:center;font-size:0.75rem">
        <b>${lat.toFixed(6)}, ${lng.toFixed(6)}</b><br>
        <button onclick="addWaypoint(${lat},${lng});map.closePopup()"
          style="margin-top:5px;padding:3px 10px;background:#5b8dee;border:none;border-radius:4px;color:#fff;cursor:pointer">
          ➕ 加為中繼點
        </button>
        <button onclick="map.removeLayer(gotoMarker);gotoMarker=null;map.closePopup()"
          style="margin-top:5px;margin-left:4px;padding:3px 10px;background:#555;border:none;border-radius:4px;color:#fff;cursor:pointer">
          ✕ 移除
        </button>
      </div>`
    ).openPopup();
  }, 1300);
}

// ── 路線計算 ──
async function fetchRoute() {
  if (document.getElementById('straight').checked) { straightRoute(); return; }
  document.getElementById('info-text').textContent='🔍 規劃路線中...';
  const res = await fetch('/route',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({waypoints})});
  const data = await res.json();
  if (data.error) { document.getElementById('info-text').textContent='❌ '+data.error; return; }
  if (routeLayer) map.removeLayer(routeLayer);
  routeCoords=data.coords; routeDistKm=data.dist_km;
  routeLayer=L.polyline(routeCoords.map(c=>[c.lat,c.lng]),{color:'#7ee8a2',weight:4,opacity:0.85}).addTo(map);
  map.fitBounds(routeLayer.getBounds(),{padding:[30,30]});
  updateRouteInfo(); updateUI(); saveRouteState();
}

function straightRoute() {
  if (routeLayer) map.removeLayer(routeLayer);
  routeCoords = waypoints.map(w=>({lat:w.lat, lng:w.lng}));
  let dist=0;
  for (let i=0;i<waypoints.length-1;i++)
    dist+=haversineJS(waypoints[i].lat,waypoints[i].lng,waypoints[i+1].lat,waypoints[i+1].lng);
  routeDistKm=Math.round(dist/10)/100;
  routeLayer=L.polyline(routeCoords.map(c=>[c.lat,c.lng]),
    {color:'#f0c040',weight:4,opacity:0.9,dashArray:'10,6'}).addTo(map);
  map.fitBounds(routeLayer.getBounds(),{padding:[30,30]});
  updateRouteInfo(); updateUI(); saveRouteState();
}

function updateRouteInfo() {
  const spd=parseFloat(document.getElementById('speed').value);
  const eta=Math.round(routeDistKm/(spd/3.6)/60*10)/10;
  document.getElementById('info-text').textContent=`📍 ${waypoints.length} 個中繼點 ｜ ${routeDistKm} km ｜ 模擬約 ${eta} 分鐘`;
}

// ── 開始 / 停止 ──
function onMushroomModeChange() {
  const on = document.getElementById('mushroom-mode').checked;
  document.getElementById('mushroom-dwell-row').style.display = on ? 'flex' : 'none';
  if (on) {
    document.getElementById('flower-mode').checked = false; onFlowerModeChange();
    document.getElementById('circle-mode').checked = false; onCircleModeChange();
  }
  const btn = document.getElementById('btn-start');
  if (waypoints.length > 0 && phoneConnected) btn.disabled = false;
  btn.textContent = on ? '🍄 開始尋菇' : '▶ 開始';
}

function onFlowerModeChange() {
  const on = document.getElementById('flower-mode').checked;
  document.getElementById('flower-settings').style.display = on ? 'flex' : 'none';
  if (!on) {
    flowerConfirmed = false;
    document.getElementById('flower-confirmed').style.display = 'none';
    if (flowerPinMarker) { map.removeLayer(flowerPinMarker); flowerPinMarker = null; }
  }
  if (on) { document.getElementById('mushroom-mode').checked = false; onMushroomModeChange(); }
  updateUI();
}

let flowerConfirmed = false;
let flowerPinMarker = null;

function flowerUseMapCenter() {
  const c = map.getCenter();
  document.getElementById('flower-coord').value =
    c.lat.toFixed(6) + ',' + c.lng.toFixed(6);
  flowerConfirmCoord();
}

function flowerConfirmCoord() {
  const raw = document.getElementById('flower-coord').value.trim();
  const parts = raw.split(',');
  if (parts.length !== 2) { alert('格式錯誤，請輸入「緯度,經度」'); return; }
  const lat = parseFloat(parts[0]), lng = parseFloat(parts[1]);
  if (isNaN(lat) || isNaN(lng)) { alert('座標數值無效'); return; }

  if (flowerPinMarker) map.removeLayer(flowerPinMarker);
  flowerPinMarker = L.marker([lat, lng], {
    icon: L.divIcon({className:'', html:'<div style="font-size:20px;line-height:1">🌸</div>', iconSize:[24,24], iconAnchor:[12,12]})
  }).addTo(map).bindPopup(`目標點<br>${lat.toFixed(5)}, ${lng.toFixed(5)}`).openPopup();
  map.panTo([lat, lng]);

  flowerConfirmed = true;
  document.getElementById('flower-confirmed').style.display = '';
  updateUI();
}

async function startFlower() {
  const raw = document.getElementById('flower-coord').value.trim();
  if (!raw) { alert('請輸入座標或按「📍 地圖中心」'); return; }
  const parts = raw.split(',');
  if (parts.length !== 2) { alert('格式錯誤，請輸入「緯度,經度」'); return; }
  const lat = parseFloat(parts[0]), lng = parseFloat(parts[1]);
  if (isNaN(lat) || isNaN(lng)) { alert('座標數值無效'); return; }
  savedRunConfig = {type: 'flower', lat, lng};
  userStopped = false;

  const res = await fetch('/start_flower', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({lat, lng})});
  const data = await res.json();
  if (data.error) { alert('❌ '+data.error); return; }

  isRunning = true;
  document.getElementById('btn-start').style.display = 'none';
  document.getElementById('btn-stop').style.display = '';
  document.getElementById('btn-goldpot').style.display = '';
  document.getElementById('progress-fill').style.width = '0%';
  document.getElementById('progress-text').textContent = '';
  document.getElementById('stat-walked').style.display = 'none';
  document.getElementById('stat-eta').style.display = '';
  document.getElementById('stat-eta').textContent = '🌸 瞬移中';
  document.getElementById('info-text').textContent = '🌸 瞬間移動 定點微漂移中';

  if (posMarker) map.removeLayer(posMarker);
  posMarker = L.marker([lat, lng], {
    icon: L.divIcon({className:'', html:'<div style="font-size:24px;line-height:1">🌸</div>', iconSize:[28,28], iconAnchor:[14,14]})
  }).addTo(map);
  map.panTo([lat, lng]);

  connectSSE();
}

// ── 繞圈種花 ──
let circleConfirmed = false;
let circlePinMarker = null;
let circleRingLayer = null;

function onCircleModeChange() {
  const on = document.getElementById('circle-mode').checked;
  document.getElementById('circle-settings').style.display = on ? 'flex' : 'none';
  if (!on) {
    circleConfirmed = false;
    document.getElementById('circle-confirmed').style.display = 'none';
    if (circlePinMarker) { map.removeLayer(circlePinMarker); circlePinMarker = null; }
    if (circleRingLayer) { map.removeLayer(circleRingLayer); circleRingLayer = null; }
  }
  if (on) {
    document.getElementById('mushroom-mode').checked = false; onMushroomModeChange();
    document.getElementById('flower-mode').checked = false; onFlowerModeChange();
  }
  updateUI();
}

function circleUseMapCenter() {
  const c = map.getCenter();
  document.getElementById('circle-coord').value = c.lat.toFixed(6) + ',' + c.lng.toFixed(6);
  circleConfirmCoord();
}

function circleConfirmCoord() {
  const raw = document.getElementById('circle-coord').value.trim();
  const parts = raw.split(',');
  if (parts.length !== 2) { alert('格式錯誤，請輸入「緯度,經度」'); return; }
  const lat = parseFloat(parts[0]), lng = parseFloat(parts[1]);
  if (isNaN(lat) || isNaN(lng)) { alert('座標數值無效'); return; }
  const radius = parseInt(document.getElementById('circle-radius').value) || 20;

  if (circlePinMarker) map.removeLayer(circlePinMarker);
  if (circleRingLayer) map.removeLayer(circleRingLayer);

  circlePinMarker = L.marker([lat, lng], {
    icon: L.divIcon({className:'', html:'<div style="font-size:20px;line-height:1">🚶</div>', iconSize:[24,24], iconAnchor:[12,12]})
  }).addTo(map).bindPopup(`繞圈中心<br>${lat.toFixed(5)}, ${lng.toFixed(5)}<br>半徑 ${radius}m`).openPopup();
  circleRingLayer = L.circle([lat, lng], {radius, color:'#7ee8a2', weight:2, fill:false, dashArray:'6,4'}).addTo(map);
  map.panTo([lat, lng]);

  circleConfirmed = true;
  document.getElementById('circle-confirmed').style.display = '';
  updateUI();
}

document.getElementById('circle-radius').addEventListener('input', () => {
  if (circleConfirmed) circleConfirmCoord();
});

async function startCircle() {
  const raw = document.getElementById('circle-coord').value.trim();
  const parts = raw.split(',');
  const lat = parseFloat(parts[0]), lng = parseFloat(parts[1]);
  const radius_m = parseInt(document.getElementById('circle-radius').value) || 20;
  savedRunConfig = {type: 'circle', lat, lng, radius_m};
  userStopped = false;

  const res = await fetch('/start_circle', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({lat, lng, radius_m, speed_kmh: 4})});
  const data = await res.json();
  if (data.error) { alert('❌ '+data.error); return; }

  isRunning = true;
  document.getElementById('btn-start').style.display = 'none';
  document.getElementById('btn-stop').style.display = '';
  document.getElementById('btn-goldpot').style.display = '';
  document.getElementById('progress-fill').style.width = '0%';
  document.getElementById('progress-text').textContent = '';
  document.getElementById('stat-walked').style.display = 'none';
  document.getElementById('stat-eta').style.display = '';
  document.getElementById('stat-eta').textContent = '🚶 繞圈中';
  document.getElementById('info-text').textContent = `🚶 繞圈種花 r=${radius_m}m @ 4km/h`;

  if (posMarker) map.removeLayer(posMarker);
  posMarker = L.marker([lat, lng], {
    icon: L.divIcon({className:'', html:'<div style="font-size:24px;line-height:1">🚶</div>', iconSize:[28,28], iconAnchor:[14,14]})
  }).addTo(map);

  connectSSE();
}

async function startPatrol() {
  if (waypoints.length < 1) { alert('請至少設定一個中繼點（蘑菇位置）'); return; }
  const dwell = parseFloat(document.getElementById('dwell-minutes').value) || 5;
  const patrolLoop = document.getElementById('patrol-loop').checked;
  const pts = waypoints.map(w => ({lat: w.lat, lng: w.lng}));
  savedRunConfig = {type: 'patrol'};
  userStopped = false;

  const res = await fetch('/start_patrol', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({waypoints: pts, dwell_minutes: dwell, patrol_loop: patrolLoop})});
  const data = await res.json();
  if (data.error) { alert('❌ '+data.error); return; }

  isRunning = true;
  if (markerMode) { markerMode=false; activeMarkerType=null; document.querySelectorAll('.btn-mtype').forEach(b=>b.classList.remove('active')); map.getContainer().style.cursor=''; }
  wpMarkers.forEach(m=>{ if(m.dragging) m.dragging.disable(); });
  document.getElementById('btn-start').style.display = 'none';
  document.getElementById('btn-stop').style.display = '';
  document.getElementById('btn-goldpot').style.display = '';
  document.getElementById('progress-fill').style.width = '0%';
  document.getElementById('progress-text').textContent = '0%';
  document.getElementById('stat-walked').style.display = 'none';
  document.getElementById('stat-eta').style.display = '';
  document.getElementById('stat-eta').textContent = '⏱ 巡邏中...';
  document.getElementById('info-text').textContent = `🍄 巡邏 0/${pts.length} 點`;

  if (posMarker) map.removeLayer(posMarker);
  posMarker = L.marker([pts[0].lat, pts[0].lng], {
    icon: L.divIcon({className:'', html:'<div style="font-size:24px;line-height:1">🍄</div>', iconSize:[28,28], iconAnchor:[14,14]})
  }).addTo(map);

  connectSSE();
}

async function startSim() {
  if (document.getElementById('mushroom-mode').checked) { await startPatrol(); return; }
  if (document.getElementById('flower-mode').checked) { await startFlower(); return; }
  if (document.getElementById('circle-mode').checked) { await startCircle(); return; }
  if (routeCoords.length<2) return;
  const speed=parseFloat(document.getElementById('speed').value);
  const loop=document.getElementById('loop').checked;
  savedRunConfig = {type: 'walk'};
  userStopped = false;

  if (lastStopPos && routeCoords.length>0) {
    const dist=haversineJS(lastStopPos.lat,lastStopPos.lng,routeCoords[0].lat,routeCoords[0].lng);
    if (dist>500) {
      if (!confirm(`⚠️ 暖機警告\n新起點距上次停止約 ${(dist/1000).toFixed(1)} km\n瞬移可能被 Niantic 偵測！\n確定繼續？`)) return;
    }
  }

  const res=await fetch('/start',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({route:routeCoords,speed,loop})});
  const data=await res.json();
  if (data.error) { alert('❌ '+data.error); return; }

  isRunning=true;
  if (markerMode) { markerMode=false; activeMarkerType=null; document.querySelectorAll('.btn-mtype').forEach(b=>b.classList.remove('active')); map.getContainer().style.cursor=''; }
  wpMarkers.forEach(m=>{ if(m.dragging) m.dragging.disable(); });
  document.getElementById('btn-start').style.display='none';
  document.getElementById('btn-stop').style.display='';
  document.getElementById('btn-goldpot').style.display='';
  document.getElementById('progress-fill').style.width='0%';
  document.getElementById('progress-text').textContent='0%';
  document.getElementById('stat-walked').style.display='';
  document.getElementById('stat-walked').textContent='🚶 0 m';
  document.getElementById('stat-eta').style.display=loop?'none':'';
  document.getElementById('stat-eta').textContent='⏱ 計算中...';

  if (posMarker) map.removeLayer(posMarker);
  posMarker=L.marker([routeCoords[0].lat,routeCoords[0].lng],{
    icon:L.divIcon({className:'',html:'<div style="font-size:24px;line-height:1">🌱</div>',iconSize:[28,28],iconAnchor:[14,14]})
  }).addTo(map);

  connectSSE();
}

function connectSSE() {
  const loop=document.getElementById('loop').checked;
  if (eventSource) eventSource.close();
  eventSource=new EventSource('/stream');
  eventSource.onerror=async ()=>{
    if (!isRunning) return;
    try {
      const s=await (await fetch('/status')).json();
      if (!s.running) onStopped();
    } catch(_) {}
  };
  eventSource.onmessage=e=>{
    const d=JSON.parse(e.data);
    if (d.ping) return;
    if (d.stopped) { onStopped(); return; }
    if (d.lat!=null) {
      posMarker.setLatLng([d.lat,d.lng]);
      if (document.getElementById('auto-follow').checked)
        map.panTo([d.lat,d.lng],{animate:true,duration:0.5});
      if (d.dwell_pct == null) {
        const pct=Math.round(d.progress);
        document.getElementById('progress-fill').style.width=pct+'%';
        document.getElementById('progress-text').textContent=pct+'%';
      }
    }
    if (d.walked_m!=null) {
      const wm=d.walked_m;
      document.getElementById('stat-walked').textContent=
        '🚶 '+(wm>=1000?(wm/1000).toFixed(2)+' km':Math.round(wm)+' m');
    }
    if (d.remaining_min!=null && !loop) {
      const rm=d.remaining_min;
      document.getElementById('stat-eta').textContent='⏱ 剩 '+(rm<1?'<1':Math.round(rm))+' 分';
    }
    if (d.loop_lap) {
      document.getElementById('info-text').textContent=`🔄 折返第 ${d.loop_lap} 圈，累計 ${d.walked_km} km`;
      document.getElementById('stat-eta').textContent=`🔄 第 ${d.loop_lap} 圈`;
    }
    if (d.arrived && !d.loop_lap)
      document.getElementById('info-text').textContent=loop?'🔄 折返中...':'🏁 抵達終點！';
    if (d.patrol_idx != null) {
      const rem = d.patrol_remaining || 0;
      const m = Math.floor(rem / 60), s = String(Math.floor(rem % 60)).padStart(2, '0');
      const lapStr = (d.patrol_loop && d.patrol_lap > 1) ? ` 第${d.patrol_lap}圈` : '';
      document.getElementById('info-text').textContent = `🍄${lapStr} 第 ${d.patrol_idx}/${d.patrol_total} 點  ⏱ ${m}:${s}`;
      document.getElementById('stat-eta').textContent = `⏱ ${m}:${s}`;
      if (d.dwell_pct != null) {
        const pct = Math.round(d.dwell_pct);
        document.getElementById('progress-fill').style.width = pct + '%';
        document.getElementById('progress-text').textContent = pct + '%';
      }
    }
    if (d.patrol_lap_done)
      document.getElementById('info-text').textContent = `🔄 第 ${d.patrol_lap} 圈完成，繼續循環...`;
    if (d.patrol_done)
      document.getElementById('info-text').textContent = '✅ 尋菇完成！';
    if (d.goldpot_countdown != null) {
      document.getElementById('goldpot-timer').textContent = d.goldpot_countdown;
      document.getElementById('info-text').textContent = `🪣 凍結GPS 倒數 ${d.goldpot_countdown}s...`;
    }
    if (d.goldpot_go) {
      const ov = document.getElementById('goldpot-overlay');
      ov.style.background = 'rgba(120,80,0,0.95)';
      document.getElementById('goldpot-title').textContent = '立刻互動金盆！';
      document.getElementById('goldpot-sub').textContent = 'DVT 已斷線，趕快在 Pikmin Bloom 互動（搭配 IPLocate 效果最佳）';
      document.getElementById('goldpot-timer').textContent = '⚡';
      document.getElementById('info-text').textContent = '🪣 DVT 已斷線！立刻互動金盆！';
    }
  };
}

async function stopSim() {
  userStopped = true;
  await fetch('/stop',{method:'POST'});
  document.getElementById('info-text').textContent='🛑 停止中...';
}

async function startGoldpot() {
  const r = await fetch('/start_goldpot', {method: 'POST'});
  const data = await r.json();
  if (!data.ok) { alert('失敗：' + (data.error||'')); return; }

  document.getElementById('btn-goldpot').style.display = 'none';
  document.getElementById('info-text').textContent = '🪣 倒數中，快切到 Pikmin Bloom...';

  const ov = document.getElementById('goldpot-overlay');
  ov.style.background = 'rgba(0,0,0,0.9)';
  ov.style.display = 'flex';
  document.getElementById('goldpot-title').textContent = '快切到 Pikmin Bloom！';
  document.getElementById('goldpot-sub').textContent = '切過去後一直不斷點金盆，3 秒後自動清除 DVT';
  document.getElementById('goldpot-timer').textContent = '3';
}

function onStopped() {
  isRunning=false;
  if (posMarker) { const ll=posMarker.getLatLng(); lastStopPos={lat:ll.lat,lng:ll.lng}; }
  wpMarkers.forEach(m=>{ if(m.dragging) m.dragging.enable(); });
  if (eventSource) { eventSource.close(); eventSource=null; }
  document.getElementById('btn-stop').style.display='none';
  document.getElementById('btn-start').style.display='';
  document.getElementById('btn-goldpot').style.display='none';
  document.getElementById('stat-eta').style.display='none';
  if (afkMode && !userStopped) {
    autoReconnect();
  } else {
    document.getElementById('info-text').textContent='✅ 已停止，恢復真實定位';
  }
}

document.getElementById('speed').addEventListener('input',function(){
  document.getElementById('speed-val').textContent=parseFloat(this.value).toFixed(1)+' km/h';
  if (routeDistKm) updateRouteInfo();
  saveRouteState();
});
document.getElementById('straight').addEventListener('change',function(){
  if (waypoints.length>=2) fetchRoute();
});

function updateUI() {
  const mushroomMode = document.getElementById('mushroom-mode').checked;
  const flowerMode = document.getElementById('flower-mode').checked;
  const circleMode = document.getElementById('circle-mode').checked;
  let has;
  if (flowerMode) {
    has = flowerConfirmed;
  } else if (circleMode) {
    has = circleConfirmed;
  } else if (mushroomMode) {
    has = waypoints.length >= 1;
  } else {
    has = routeCoords.length >= 2;
  }
  document.getElementById('btn-start').disabled = !(has && phoneConnected);
  document.getElementById('btn-start').textContent =
    mushroomMode ? '🍄 開始尋菇' : flowerMode ? '🌸 瞬間移動' : circleMode ? '🚶 開始繞圈' : '▶ 開始';
  document.getElementById('btn-save').disabled = routeCoords.length < 2;
  const sel = document.getElementById('route-select');
  document.getElementById('btn-export').disabled = !sel || !sel.value;
  document.getElementById('btn-goldpot').style.display = (phoneConnected && isRunning) ? '' : 'none';
}

// ── 掛機模式 ──
let afkMode = false, savedRunConfig = null, userStopped = false;

function toggleAfkMode() {
  afkMode = !afkMode;
  const btn = document.getElementById('btn-afk');
  btn.classList.toggle('afk-on', afkMode);
  btn.textContent = afkMode ? '🌙 掛機中' : '🌙 掛機模式';
  document.getElementById('info-text').textContent = afkMode
    ? '🌙 掛機模式已開啟，斷線將自動重連'
    : '🌙 掛機模式已關閉';
}

async function autoReconnect() {
  if (!afkMode || !savedRunConfig) return;
  document.getElementById('info-text').textContent = '🔄 偵測到斷線，5 秒後自動重連...';
  await new Promise(r => setTimeout(r, 5000));
  if (!afkMode) return;

  document.getElementById('info-text').textContent = '🔄 重連中，請稍候...';
  // 重新連線
  const btn = document.getElementById('btn-connect');
  btn.textContent = '⏳ 連線中...'; btn.disabled = true;
  btn.style.background = '#888'; btn.style.color = '#fff';
  try {
    const res = await fetch('/connect_phone', {method:'POST'});
    const data = await res.json();
    if (data.ok) {
      phoneConnected = true;
      btn.textContent = '📱 已連線'; btn.style.background = '#7ee8a2'; btn.style.color = '#1a1a2e';
      btn.disabled = false;
      updateUI();
      // 重啟上次的模式
      await new Promise(r => setTimeout(r, 1500));
      if (!afkMode) return;
      const rt = savedRunConfig.type;
      if (rt === 'patrol') {
        await startPatrol();
      } else if (rt === 'flower') {
        document.getElementById('flower-coord').value = savedRunConfig.lat+','+savedRunConfig.lng;
        await startFlower();
      } else if (rt === 'circle') {
        document.getElementById('circle-coord').value = savedRunConfig.lat+','+savedRunConfig.lng;
        document.getElementById('circle-radius').value = savedRunConfig.radius_m || 20;
        await startCircle();
      } else {
        await startSim();
      }
    } else {
      btn.textContent = '🔌 連線手機'; btn.disabled = false;
      btn.style.background = '#4a4a6a'; btn.style.color = '#ccc';
      document.getElementById('info-text').textContent = '❌ 重連失敗：' + data.message + '，請手動重連';
    }
  } catch {
    btn.textContent = '🔌 連線手機'; btn.disabled = false;
    btn.style.background = '#4a4a6a'; btn.style.color = '#ccc';
    document.getElementById('info-text').textContent = '❌ 重連異常，請手動重連';
  }
}

async function connectPhone() {
  const btn=document.getElementById('btn-connect');
  btn.textContent='⏳ 偵測中...'; btn.disabled=true;
  btn.style.background='#888'; btn.style.color='#fff';
  try {
    const st = await (await fetch('/api/setup/state')).json();
    if (st.status !== 'ready') {
      btn.textContent='🔌 連線手機'; btn.disabled=false;
      btn.style.background='#4a4a6a'; btn.style.color='#ccc';
      openSetupWizard(st);
      return;
    }
  } catch(e) {}
  await doConnectPhone();
}

async function doConnectPhone() {
  const btn=document.getElementById('btn-connect');
  btn.textContent='⏳ 連線中...'; btn.disabled=true;
  btn.style.background='#888'; btn.style.color='#fff';
  try {
    const res=await fetch('/connect_phone',{method:'POST'});
    const data=await res.json();
    if(data.ok){
      phoneConnected=true;
      btn.textContent='📱 已連線';
      btn.style.background='#7ee8a2'; btn.style.color='#1a1a2e';
      document.getElementById('info-text').textContent='✅ '+data.message;
      updateUI();
    } else {
      btn.textContent='🔌 連線手機'; btn.disabled=false;
      btn.style.background='#e87e7e'; btn.style.color='#fff';
      document.getElementById('info-text').textContent='❌ '+data.message;
      setTimeout(()=>{btn.style.background='#4a4a6a';btn.style.color='#ccc';},3000);
    }
  } catch(e){
    btn.textContent='🔌 連線手機'; btn.disabled=false;
    btn.style.background='#4a4a6a'; btn.style.color='#ccc';
  }
}

// ── 設定精靈 ──
let setupCurrentStep = 0;
let setupRebootSse = null;

function openSetupWizard(initialState) {
  document.getElementById('setup-overlay').classList.add('active');
  runSetupFromState(initialState);
}

function setSetupStep(step) {
  setupCurrentStep = step;
  document.getElementById('setup-progress-fill').style.width = (step / 4 * 100) + '%';
  for (let i = 0; i < 4; i++) {
    const el = document.getElementById('ss' + i);
    el.classList.toggle('active', i === step);
    el.classList.toggle('done', i < step);
    el.querySelector('.step-icon').textContent = i < step ? '✅' : ['①','②','③','④'][i];
  }
}

function setSetupMsg(msg, btnText, btnEnabled) {
  document.getElementById('setup-msg').innerHTML = msg;
  const btn = document.getElementById('setup-action-btn');
  btn.textContent = btnText;
  btn.disabled = !btnEnabled;
  btn.className = btnEnabled ? '' : '';
}

async function runSetupFromState(state) {
  if (state.status === 'ios_too_old' || state.step === -1) {
    setSetupStep(0);
    setSetupMsg(`⚠️ ${state.message || '不支援的 iOS 版本，請升級至 iOS 17 或以上。'}`, '關閉', true);
    document.getElementById('setup-action-btn').onclick = () => document.getElementById('setup-overlay').style.display='none';
  } else if (state.status === 'no_phone' || state.status === 'phone_locked' || state.step === 0) {
    setSetupStep(0);
    const stepMsg = state.status === 'phone_locked'
      ? `📱 ${state.message || '手機已偵測到，請解鎖手機螢幕後再點「偵測手機」。'}`
      : '請將 iPhone 用 USB 連接到本機，插上後點「偵測手機」。';
    setSetupMsg(stepMsg, '偵測手機', true);
    document.getElementById('setup-action-btn').onclick = async () => {
      setSetupMsg('重啟 USB 偵測中，約需 5 秒...', '請稍候', false);
      const st = await (await fetch('/api/setup/detect_phone', {method:'POST'})).json();
      runSetupFromState(st);
    };
  } else if (state.status === 'needs_trust' || state.step === 1) {
    setSetupStep(1);
    setSetupMsg('iPhone 螢幕應出現「<b>信任此電腦？</b>」，請點「<b>信任</b>」並輸入手機密碼。<br><br>點完後按下方按鈕。', '已點信任，繼續', true);
    document.getElementById('setup-action-btn').onclick = async () => {
      setSetupMsg('配對中...', '請稍候', false);
      const r = await (await fetch('/api/setup/pair', {method:'POST'})).json();
      if (r.needs_trust) {
        setSetupMsg('⚠️ 還沒信任，請先在 iPhone 上點「信任」。', '已點信任，繼續', true);
      } else if (r.ok) {
        runSetupFromState({step: 2, status: 'needs_devmode'});
      } else {
        setSetupMsg('❌ 配對失敗，請重新拔插 USB 再試。<br><small>' + (r.output||'') + '</small>', '重試', true);
        document.getElementById('setup-action-btn').onclick = async () => runSetupFromState({step:1, status:'needs_trust'});
      }
    };
  } else if (state.status === 'needs_devmode' || state.step === 2) {
    setSetupStep(2);
    setSetupMsg('正在讓「開發者模式」出現在設定裡...', '請稍候', false);
    const r = await (await fetch('/api/setup/reveal_devmode', {method:'POST'})).json();
    setSetupMsg('請去 iPhone：<br>📱 <b>設定 → 隱私權與安全性 → 開發者模式 → 開啟</b><br><br>手機會要求<b>重新開機</b>，重開後回來按下方按鈕。', '手機重開完成，繼續', true);
    document.getElementById('setup-action-btn').onclick = () => {
      const goMount = () => {
        if (setupRebootSse) { setupRebootSse.close(); setupRebootSse = null; }
        runSetupFromState({step: 3, status: 'needs_mount'});
      };
      setSetupMsg('等待手機重開並重新連接...<br><small>手機解鎖後會自動繼續</small>', '手機已解鎖，直接繼續 →', true);
      document.getElementById('setup-action-btn').onclick = goMount;
      if (setupRebootSse) setupRebootSse.close();
      setupRebootSse = new EventSource('/api/setup/wait_reboot');
      setupRebootSse.onmessage = e => {
        const d = JSON.parse(e.data);
        if (d.status === 'disconnected') {
          setSetupMsg('手機重開中，等待重新連接...<br><small>解鎖後會自動繼續，或手動點按鈕</small>', '手機已解鎖，直接繼續 →', true);
          document.getElementById('setup-action-btn').onclick = goMount;
        } else if (d.status === 'reconnected') {
          goMount();
        } else if (d.status === 'timeout') {
          if (setupRebootSse) { setupRebootSse.close(); setupRebootSse = null; }
          setSetupMsg('⚠️ 自動偵測逾時。<br>請確認手機已解鎖並插上 USB，然後點繼續。', '繼續到掛載步驟 →', true);
          document.getElementById('setup-action-btn').onclick = () => runSetupFromState({step: 3, status: 'needs_mount'});
        }
      };
    };
  } else if (state.step === 3 || state.status === 'needs_mount') {
    setSetupStep(3);
    setSetupMsg('正在安裝開發工具（需連網，約 30–120 秒）...', '請稍候', false);
    let r;
    try {
      r = await (await fetch('/api/setup/mount', {method:'POST'})).json();
    } catch(e) {
      setSetupMsg('❌ 網路錯誤，無法完成安裝。<br><small>' + e.message + '</small>', '重試', true);
      document.getElementById('setup-action-btn').onclick = () => runSetupFromState({step:3, status:'needs_mount'});
      return;
    }
    if (r.ok) {
      setSetupStep(4);
      document.getElementById('setup-progress-fill').style.width = '100%';
      setSetupMsg('✅ <b>設定完成！</b><br><br>此手機日後插上即可直接使用，無需重複設定。', '開始連線', true);
      document.getElementById('setup-action-btn').className = 'success';
      document.getElementById('setup-action-btn').onclick = async () => {
        document.getElementById('setup-overlay').classList.remove('active');
        await doConnectPhone();
      };
    } else {
      setSetupMsg('❌ 安裝失敗，請確認網路正常。<br><small>' + (r.output||'').slice(0,120) + '</small>', '重試', true);
      document.getElementById('setup-action-btn').onclick = () => runSetupFromState({step:3, status:'needs_mount'});
    }
  } else if (state.status === 'ready') {
    document.getElementById('setup-overlay').classList.remove('active');
    await doConnectPhone();
  }
}

// ── 搜尋 ──
async function searchPlace() {
  const q=document.getElementById('search-input').value.trim(); if(!q) return;
  const btn=document.getElementById('btn-search');
  btn.textContent='...'; btn.disabled=true;
  const box=document.getElementById('search-results');
  box.innerHTML=''; box.style.display='block';
  try {
    const res=await fetch('/geocode?q='+encodeURIComponent(q));
    const results=await res.json();
    if (!results.length||results.error) { box.innerHTML='<div style="color:#888">找不到結果</div>'; return; }
    results.forEach(r=>{
      const div=document.createElement('div');
      div.textContent=r.name;
      div.onclick=()=>{ map.setView([r.lat,r.lng],16); box.style.display='none'; document.getElementById('search-input').value=''; };
      box.appendChild(div);
    });
  } catch { box.innerHTML='<div style="color:#e87e7e">搜尋失敗</div>'; }
  finally { btn.textContent='搜尋'; btn.disabled=false; }
}
document.addEventListener('click',e=>{ if(!e.target.closest('.search-wrap')) document.getElementById('search-results').style.display='none'; });

// ── 路線儲存／載入 ──
async function refreshRouteList() {
  const routes=(await (await fetch('/list_routes')).json());
  const sel=document.getElementById('route-select');
  sel.innerHTML='<option value="">-- 選擇路線 --</option>';
  routes.forEach(r=>{ const o=document.createElement('option'); o.value=r.filename; o.textContent=`${r.name}（${r.dist_km} km，${r.created}）`; sel.appendChild(o); });
  document.getElementById('btn-load').disabled=routes.length===0;
}

async function saveRoute() {
  const name=document.getElementById('route-name').value.trim();
  if (!name) { alert('請輸入路線名稱'); return; }
  const res=await fetch('/save_route',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({name,waypoints,route_coords:routeCoords,dist_km:routeDistKm})});
  const data=await res.json();
  if (data.error) { alert('❌ '+data.error); return; }
  document.getElementById('route-name').value='';
  await refreshRouteList();
  document.getElementById('info-text').textContent=`✅ 路線「${name}」已儲存`;
}

async function loadRoute() {
  const filename=document.getElementById('route-select').value; if(!filename) return;
  const data=await (await fetch('/load_route/'+encodeURIComponent(filename))).json();
  if (data.error) { alert('❌ '+data.error); return; }
  clearAll(); loadingRoute=true;
  (data.waypoints||[]).forEach(wp=>addWaypoint(wp.lat,wp.lng));
  loadingRoute=false;
  if (data.route_coords&&data.route_coords.length>=2) {
    routeCoords=data.route_coords; routeDistKm=data.dist_km||0;
    if (routeLayer) map.removeLayer(routeLayer);
    routeLayer=L.polyline(routeCoords.map(c=>[c.lat,c.lng]),{color:'#7ee8a2',weight:4,opacity:0.85}).addTo(map);
    map.fitBounds(routeLayer.getBounds(),{padding:[30,30]});
  }
  updateRouteInfo(); updateUI(); saveRouteState();
}

async function deleteRoute() {
  const sel=document.getElementById('route-select'); if(!sel.value) return;
  if (!confirm(`確定刪除「${sel.options[sel.selectedIndex].text}」？`)) return;
  await fetch('/delete_route/'+encodeURIComponent(sel.value),{method:'DELETE'});
  await refreshRouteList();
}
document.getElementById('route-select').addEventListener('change',function(){
  document.getElementById('btn-load').disabled=!this.value;
  document.getElementById('btn-export').disabled=!this.value;
});

function exportRoute() {
  const sel=document.getElementById('route-select'); if(!sel.value) return;
  window.location.href = '/export_route/' + encodeURIComponent(sel.value);
}

async function importRoute(event) {
  const file=event.target.files[0]; if(!file) return;
  const fd=new FormData(); fd.append('file',file);
  const r=await fetch('/api/import_route',{method:'POST',body:fd});
  const d=await r.json();
  if (d.error) { alert('匯入失敗：'+d.error); return; }
  alert('匯入成功：'+d.saved);
  await refreshRouteList();
  event.target.value='';
}

// ── 實體搖桿 ──
let joystickRunning = false;

async function setJoyMode(m) {
  await fetch('/api/joystick/mode',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({mode:m})});
  document.getElementById('btn-mode-coarse').style.background = m==='coarse'?'#7c6cd4':'#444';
  document.getElementById('btn-mode-coarse').style.color = m==='coarse'?'#fff':'#aaa';
  document.getElementById('btn-mode-fine').style.background = m==='fine'?'#7c6cd4':'#444';
  document.getElementById('btn-mode-fine').style.color = m==='fine'?'#fff':'#aaa';
  document.getElementById('coarse-steps').style.display = m==='coarse'?'flex':'none';
}

async function setJoyStep(s) {
  await fetch('/api/joystick/mode',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({step_m:s})});
  [50,100,200,500].forEach(v=>{
    const b=document.getElementById('btn-step-'+v);
    b.style.background=v===s?'#7c6cd4':'#444';
    b.style.color=v===s?'#fff':'#aaa';
  });
}

function toggleJoystick() {
  if (joystickRunning) {
    fetch('/stop',{method:'POST'});
    joystickRunning=false;
    document.getElementById('btn-joystick').style.background='#4a4a6a';
    document.getElementById('btn-joystick').style.color='#ccc';
  } else {
    if (!posMarker) {
      const c=map.getCenter();
      posMarker=L.marker([c.lat,c.lng],{icon:leafIcon}).addTo(map);
      state.lat=c.lat; state.lng=c.lng;
    }
    joystickRunning=true;
    document.getElementById('btn-joystick').style.background='#f59e0b';
    document.getElementById('btn-joystick').style.color='#1a1a2e';
    connectSSE();
  }
}

setInterval(async()=>{
  const dot=document.getElementById('ble-dot');
  if (!joystickRunning) { dot.style.color='#555'; return; }
  const s=await (await fetch('/status')).json();
  const age=Date.now()-(s.last_joystick_ms||0);
  dot.style.color=age<4000?'#7ee8a2':'#555';
},2000);

setInterval(async()=>{
  try {
    const r=await (await fetch('/api/steps/peek')).json();
    document.getElementById('steps-pending').textContent=r.steps.toLocaleString()+' 步';
    document.getElementById('steps-today').textContent=r.today_claimed.toLocaleString();
    const pct=Math.min(100,r.today_claimed/r.daily_max*100);
    document.getElementById('steps-daily-bar').style.width=pct+'%';
    document.getElementById('steps-daily-bar').style.background=pct>=100?'#e85050':'#7ee8a2';
  } catch(_){}
},5000);

// ── GPX 匯入 ──
function importGPX(event) {
  const file=event.target.files[0]; if(!file) return;
  const reader=new FileReader();
  reader.onload=e=>{
    const xml=new DOMParser().parseFromString(e.target.result,'text/xml');
    const trkpts=[...xml.querySelectorAll('trkpt')];
    const wpts=[...xml.querySelectorAll('wpt')];
    if (trkpts.length>=2) {
      const coords=trkpts.map(p=>({lat:+p.getAttribute('lat'),lng:+p.getAttribute('lon')}));
      let dist=0; for(let i=1;i<coords.length;i++) dist+=haversineJS(coords[i-1].lat,coords[i-1].lng,coords[i].lat,coords[i].lng);
      clearAll();
      const N=Math.min(8,coords.length), step=Math.floor((coords.length-1)/Math.max(1,N-1));
      const idxs=[]; for(let i=0;i<N-1;i++) idxs.push(i*step); idxs.push(coords.length-1);
      loadingRoute=true; idxs.forEach(i=>addWaypoint(coords[i].lat,coords[i].lng)); loadingRoute=false;
      routeCoords=coords; routeDistKm=Math.round(dist/100)/10;
      if(routeLayer) map.removeLayer(routeLayer);
      routeLayer=L.polyline(coords.map(c=>[c.lat,c.lng]),{color:'#7ee8a2',weight:4,opacity:0.85}).addTo(map);
      map.fitBounds(routeLayer.getBounds(),{padding:[30,30]}); updateRouteInfo(); updateUI(); saveRouteState();
    } else if (wpts.length>=2) {
      clearAll(); wpts.forEach(p=>addWaypoint(+p.getAttribute('lat'),+p.getAttribute('lon')));
    } else { alert('GPX 找不到路線資料'); }
  };
  reader.readAsText(file); event.target.value='';
}


// ── OTA 更新 ──
(async()=>{
  try {
    const r=await(await fetch('/api/version')).json();
    document.getElementById('update-current').textContent='v'+r.version;
    document.getElementById('ver-tag').textContent='v'+r.version;
  } catch(_){}
})();

async function checkUpdate(){
  const btn=document.getElementById('btn-update-check');
  const res=document.getElementById('update-result');
  const applyBtn=document.getElementById('btn-update-apply');
  btn.disabled=true; btn.textContent='🔍 檢查中...';
  res.style.display='none'; applyBtn.style.display='none';
  try {
    const r=await(await fetch('/api/update/check')).json();
    if(r.error){ res.innerHTML='<span style="color:#e85050">❌ '+r.error+'</span>'; }
    else if(r.has_update){
      res.innerHTML='<b style="color:#e8a040">🆕 有新版本 v'+r.latest+'</b><br>'+
        (r.changelog?'<span style="color:#999">'+r.changelog+'</span>':'');
      applyBtn.style.display='';
    } else {
      res.innerHTML='<span style="color:#7ee8a2">✅ 已是最新版本 v'+r.current+'</span>';
    }
    res.style.display='block';
  } catch(e){
    res.innerHTML='<span style="color:#e85050">❌ 連線失敗，請確認 iPhone 已插上</span>';
    res.style.display='block';
  }
  btn.disabled=false; btn.textContent='🔍 檢查更新';
}

async function applyUpdate(){
  if(!confirm('確定要更新嗎？更新後會自動重啟。')) return;
  const btn=document.getElementById('btn-update-apply');
  const res=document.getElementById('update-result');
  btn.disabled=true; btn.textContent='⬆ 更新中...';
  try {
    const r=await(await fetch('/api/update/apply',{method:'POST'})).json();
    if(r.error){
      res.innerHTML='<span style="color:#e85050">❌ '+r.error+'</span>';
      btn.disabled=false; btn.textContent='⬆ 立即更新';
    } else {
      res.innerHTML='<span style="color:#7ee8a2">✅ '+r.message+'</span>';
      btn.style.display='none';
      setTimeout(()=>{ res.innerHTML='<span style="color:#aaa">🔄 重新載入頁面中...</span>'; },2000);
      setTimeout(()=>{ location.reload(); },6000);
    }
  } catch(e){
    res.innerHTML='<span style="color:#e85050">❌ 更新異常：'+e+'</span>';
    btn.disabled=false; btn.textContent='⬆ 立即更新';
  }
}

// ── 說明手冊 ──
function openHelp(){ document.getElementById('help-overlay').classList.add('active'); }
function copyStepsUrl(){
  const url=location.protocol+'//'+location.host+'/api/steps';
  const ta=document.createElement('textarea');
  ta.value=url; ta.style.position='fixed'; ta.style.opacity='0';
  document.body.appendChild(ta); ta.select();
  try{ document.execCommand('copy');
    const el=document.getElementById('steps-url-copied');
    el.style.display='block'; el.textContent='✅ 已複製 '+url;
    setTimeout(()=>el.style.display='none',4000);
  }catch(e){ prompt('請手動複製這個網址：',url); }
  document.body.removeChild(ta);
}
function closeHelp(){ document.getElementById('help-overlay').classList.remove('active'); }
function toggleHs(id,arrowId){
  const el=document.getElementById(id), ar=document.getElementById(arrowId);
  const open=el.classList.toggle('open');
  ar.textContent=open?'▾':'▸';
}

// ── 地圖標記 ──
let activeMarkerType = null;
function toggleMarkerMode(type) {
  if (markerMode && activeMarkerType === type) {
    // 再次點同一個 → 離開標記模式
    markerMode = false;
    activeMarkerType = null;
  } else {
    markerMode = true;
    activeMarkerType = type;
  }
  document.querySelectorAll('.btn-mtype').forEach(b => b.classList.remove('active'));
  if (markerMode) document.getElementById('mtype-' + type).classList.add('active');
  map.getContainer().style.cursor = markerMode ? 'crosshair' : '';
}

function showMarkerForm(lat, lng, type) {
  const emoji = MARKER_ICONS[type] || '📍';
  const form = document.createElement('div');
  form.style.cssText = 'display:flex;flex-direction:column;gap:8px;min-width:195px;padding:2px';

  // 標題列（顯示目前類型）
  const title = document.createElement('div');
  title.style.cssText = 'text-align:center;font-size:1.3rem';
  title.textContent = emoji + ' ' + MARKER_NAMES[type];
  form.appendChild(title);

  // 名稱輸入
  const input = document.createElement('input');
  input.type = 'text'; input.placeholder = '標記名稱（可空白）';
  input.style.cssText = 'background:#2a2a4e;border:1px solid #3a3a6e;color:#eee;border-radius:5px;padding:5px 8px;font-size:0.85rem;width:100%';
  form.appendChild(input);

  // 按鈕列
  const btnRow = document.createElement('div'); btnRow.style.cssText = 'display:flex;gap:6px';
  const ok = document.createElement('button'); ok.textContent = '確定';
  ok.style.cssText = 'flex:1;background:#7ee8a2;color:#1a1a2e;border:none;border-radius:5px;padding:5px;cursor:pointer;font-weight:bold;font-size:0.85rem';
  const cancel = document.createElement('button'); cancel.textContent = '取消';
  cancel.style.cssText = 'flex:1;background:#4a4a6a;color:#ccc;border:none;border-radius:5px;padding:5px;cursor:pointer;font-size:0.85rem';
  btnRow.append(ok, cancel); form.appendChild(btnRow);

  L.popup({closeButton:false, maxWidth:240}).setLatLng([lat,lng]).setContent(form).openOn(map);
  setTimeout(() => input.focus(), 50);

  ok.addEventListener('click', () => {
    const name = input.value.trim() || MARKER_NAMES[type];
    map.closePopup(); addCustomMarker(lat, lng, name, type);
  });
  cancel.addEventListener('click', () => map.closePopup());
  input.addEventListener('keydown', e => { if (e.key==='Enter') ok.click(); });
}

function addCustomMarker(lat, lng, name, type='pin', save=true) {
  const emoji=MARKER_ICONS[type]||'📍';
  const marker=L.marker([lat,lng],{
    icon:L.divIcon({className:'',html:`<div style="font-size:22px;line-height:1;filter:drop-shadow(0 1px 3px #000)">${emoji}</div>`,iconSize:[26,26],iconAnchor:[13,13]})
  }).addTo(map);
  const entry={marker,name,type};
  customMarkers.push(entry);

  marker.on('click',()=>{
    const content=document.createElement('div');
    content.style.cssText='min-width:130px;padding:2px';
    content.innerHTML=`<b style="font-size:0.95rem">${emoji} ${name}</b>`;
    const del=document.createElement('button');
    del.textContent='🗑 刪除';
    del.style.cssText='display:block;margin-top:8px;padding:4px 10px;background:#e87e7e;border:none;border-radius:4px;cursor:pointer;color:#fff;font-size:0.8rem;width:100%';
    del.addEventListener('click',()=>{
      map.removeLayer(marker);
      const idx=customMarkers.indexOf(entry);
      if(idx>=0) customMarkers.splice(idx,1);
      saveCustomMarkers(); map.closePopup();
    });
    content.appendChild(del);
    L.popup({maxWidth:200}).setLatLng([lat,lng]).setContent(content).openOn(map);
  });

  if(save) saveCustomMarkers();
}

function saveCustomMarkers(){
  const data = customMarkers.map(m=>({lat:m.marker.getLatLng().lat,lng:m.marker.getLatLng().lng,name:m.name,type:m.type}));
  fetch('/api/markers',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(data)}).catch(()=>{});
}

async function loadCustomMarkers(){
  try {
    const r = await fetch('/api/markers');
    const arr = await r.json();
    arr.forEach(m => addCustomMarker(m.lat, m.lng, m.name, m.type, false));
  } catch{}
}

function saveRouteState() {
  if (routeCoords.length<2) return;
  localStorage.setItem('gpsikmin-route',JSON.stringify({
    waypoints, routeCoords, routeDistKm,
    loop: document.getElementById('loop').checked,
    straight: document.getElementById('straight').checked,
    speed: parseFloat(document.getElementById('speed').value)
  }));
}

async function restoreRouteState() {
  let saved; try { saved=JSON.parse(localStorage.getItem('gpsikmin-route')||'null'); } catch{ return; }
  if (!saved||!saved.routeCoords||saved.routeCoords.length<2) return;
  loadingRoute=true;
  (saved.waypoints||[]).forEach(wp=>addWaypoint(wp.lat,wp.lng));
  loadingRoute=false;
  routeCoords=saved.routeCoords; routeDistKm=saved.routeDistKm||0;
  if (routeLayer) map.removeLayer(routeLayer);
  routeLayer=L.polyline(routeCoords.map(c=>[c.lat,c.lng]),{color:'#7ee8a2',weight:4,opacity:0.85}).addTo(map);
  map.fitBounds(routeLayer.getBounds(),{padding:[30,30]});
  if (saved.loop!=null) document.getElementById('loop').checked=saved.loop;
  if (saved.straight!=null) document.getElementById('straight').checked=saved.straight;
  if (saved.speed!=null) {
    document.getElementById('speed').value=saved.speed;
    document.getElementById('speed-val').textContent=saved.speed.toFixed(1)+' km/h';
  }
  if (saved.straight && routeLayer) {
    map.removeLayer(routeLayer);
    routeLayer=L.polyline(routeCoords.map(c=>[c.lat,c.lng]),
      {color:'#f0c040',weight:4,opacity:0.9,dashArray:'10,6'}).addTo(map);
  }
  updateRouteInfo(); updateUI();
  try {
    const st=await (await fetch('/status')).json();
    if (st.running) {
      isRunning=true;
      // 還原手機連線狀態
      phoneConnected=true;
      const cb=document.getElementById('btn-connect');
      cb.textContent='📱 已連線'; cb.style.background='#7ee8a2'; cb.style.color='#1a1a2e'; cb.disabled=false;
      updateUI();
      document.getElementById('btn-start').style.display='none';
      document.getElementById('btn-stop').style.display='';
      const loop=document.getElementById('loop').checked;
      document.getElementById('stat-walked').style.display='';
      document.getElementById('stat-eta').style.display=loop?'none':'';
      // 還原行走進度（暫停 transition 避免從 0% 動畫）
      const fill=document.getElementById('progress-fill');
      fill.style.transition='none';
      const wm=st.walked_m||0;
      const pct=Math.round(st.progress||0);
      const rm=st.remaining_min||0;
      document.getElementById('stat-walked').textContent=
        '🚶 '+(wm>=1000?(wm/1000).toFixed(2)+' km':Math.round(wm)+' m');
      fill.style.width=pct+'%';
      document.getElementById('progress-text').textContent=pct+'%';
      if (!loop) document.getElementById('stat-eta').textContent=
        '⏱ 剩 '+(rm<1?'<1':Math.round(rm))+' 分';
      // 還原後重新啟用 transition
      requestAnimationFrame(()=>{ fill.style.transition=''; });
      // 還原位置標記
      if (st.lat!=null) {
        if (posMarker) map.removeLayer(posMarker);
        posMarker=L.marker([st.lat,st.lng],{
          icon:L.divIcon({className:'',html:'<div style="font-size:24px;line-height:1">🌱</div>',iconSize:[28,28],iconAnchor:[14,14]})
        }).addTo(map);
        map.panTo([st.lat,st.lng]);
      }
      document.getElementById('info-text').textContent='▶ 模擬中（已重新連線）';
      connectSSE();
    }
  } catch(e) {}
}

// ── 從標記選點 ──
let pmFilter = 'all';
function openPickMarkersModal() {
  document.getElementById('pickmarkers-overlay').style.display = 'block';
  document.getElementById('pickmarkers-modal').style.display = 'flex';
  renderPickList(pmFilter);
}
function closePickMarkersModal() {
  document.getElementById('pickmarkers-overlay').style.display = 'none';
  document.getElementById('pickmarkers-modal').style.display = 'none';
}
function renderPickList(filter) {
  pmFilter = filter;
  document.querySelectorAll('#pickmarkers-modal .sf-btn').forEach(b => b.classList.remove('sf-active'));
  const ab = document.getElementById('pm-' + filter);
  if (ab) ab.classList.add('sf-active');

  const list = filter === 'all' ? customMarkers : customMarkers.filter(m => m.type === filter);
  const container = document.getElementById('pm-list');
  container.innerHTML = '';
  if (!list.length) {
    container.innerHTML = '<div style="color:#888;text-align:center;padding:20px;font-size:0.72rem">尚無標記</div>';
    return;
  }
  list.forEach(entry => {
    const row = document.createElement('label');
    row.style.cssText = 'display:flex;align-items:center;gap:8px;padding:7px 10px;font-size:0.68rem;border-bottom:1px solid #1a2240;cursor:pointer';
    const cb = document.createElement('input');
    cb.type = 'checkbox'; cb.style.flexShrink = '0';
    const emoji = MARKER_ICONS[entry.type] || '📍';
    const nameSpan = document.createElement('span');
    nameSpan.style.cssText = 'flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap';
    nameSpan.textContent = emoji + ' ' + entry.name;
    row.append(cb, nameSpan);
    row.onmouseover = () => row.style.background = '#2a3a6e';
    row.onmouseout  = () => row.style.background = '';
    row._entry = entry;
    row._cb = cb;
    container.appendChild(row);
  });
}
function confirmPickMarkers() {
  const container = document.getElementById('pm-list');
  const rows = Array.from(container.querySelectorAll('label'));
  const selected = rows.filter(r => r._cb && r._cb.checked).map(r => r._entry);
  if (!selected.length) { alert('請至少勾選一個標記'); return; }
  selected.forEach(entry => {
    const ll = entry.marker.getLatLng();
    addWaypoint(ll.lat, ll.lng);
  });
  closePickMarkersModal();
}

// ── 我的標記清單 ──
let mmFilter = 'all';
function openMarkersModal() {
  document.getElementById('mymarkers-overlay').style.display = 'block';
  document.getElementById('mymarkers-modal').style.display = 'flex';
  renderMarkersList(mmFilter);
}
function closeMarkersModal() {
  document.getElementById('mymarkers-overlay').style.display = 'none';
  document.getElementById('mymarkers-modal').style.display = 'none';
}
function renderMarkersList(filter) {
  mmFilter = filter;
  document.querySelectorAll('#mymarkers-modal .sf-btn').forEach(b => b.classList.remove('sf-active'));
  const ab = document.getElementById('mm-' + filter);
  if (ab) ab.classList.add('sf-active');

  const list = filter === 'all'
    ? customMarkers
    : customMarkers.filter(m => m.type === filter);

  const container = document.getElementById('mm-list');
  container.innerHTML = '';
  if (!list.length) {
    container.innerHTML = '<div style="color:#888;text-align:center;padding:20px;font-size:0.72rem">尚無標記</div>';
    return;
  }
  list.forEach(entry => {
    const row = document.createElement('div');
    row.style.cssText = 'padding:7px 10px;cursor:pointer;font-size:0.68rem;border-bottom:1px solid #1a2240;display:flex;align-items:center;gap:6px';
    const emoji = MARKER_ICONS[entry.type] || '📍';
    const lat = entry.marker.getLatLng().lat.toFixed(4);
    const lng = entry.marker.getLatLng().lng.toFixed(4);

    const nameSpan = document.createElement('span');
    nameSpan.style.cssText = 'flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap';
    nameSpan.textContent = emoji + ' ' + entry.name;

    const coordSpan = document.createElement('span');
    coordSpan.style.cssText = 'color:#555;font-size:0.6rem;flex-shrink:0';
    coordSpan.textContent = lat + ',' + lng;

    const delBtn = document.createElement('button');
    delBtn.textContent = '✕';
    delBtn.title = '刪除';
    delBtn.style.cssText = 'background:none;border:none;color:#e87e7e;cursor:pointer;font-size:0.75rem;flex-shrink:0;padding:0 2px';
    delBtn.onclick = (e) => {
      e.stopPropagation();
      const idx = customMarkers.indexOf(entry);
      if (idx >= 0) { entry.marker.remove(); customMarkers.splice(idx, 1); saveCustomMarkers(); }
      renderMarkersList(mmFilter);
    };

    row.append(nameSpan, coordSpan, delBtn);
    row.onclick = () => { closeMarkersModal(); flyToSpot(entry.marker.getLatLng().lat, entry.marker.getLatLng().lng, entry.name, entry.type); };
    row.onmouseover = () => row.style.background = '#2a3a6e';
    row.onmouseout  = () => row.style.background = '';
    container.appendChild(row);
  });
}

// ── pogoskill 熱點載入 ──
let spotsData = null;
let spotsFilter = 'all';

const SPOT_CATEGORIES = [
  {key:'mushrooms',  label:'🍄 蘑菇',   type:'mushroom'},
  {key:'big_flowers',label:'🌸 大花',   type:'plant'},
  {key:'postcards',  label:'⭐ 明信片', type:'special'},
  {key:'taiwan_poi', label:'📍 台灣 POI',type:'pin'},
];

async function openSpotsModal() {
  document.getElementById('spots-overlay').style.display='block';
  document.getElementById('spots-modal').style.display='flex';
  if (!spotsData) {
    document.getElementById('spots-list').innerHTML='<div style="color:#888;text-align:center;padding:20px;font-size:0.72rem">載入中…</div>';
    try {
      spotsData = await (await fetch('/static/pikmin_spots.json')).json();
    } catch {
      document.getElementById('spots-list').innerHTML='<div style="color:#e87e7e;text-align:center;padding:20px;font-size:0.72rem">無法載入資料</div>';
      return;
    }
  }
  renderSpotsList(spotsFilter);
}
function closeSpotsModal() {
  document.getElementById('spots-overlay').style.display='none';
  document.getElementById('spots-modal').style.display='none';
}

function renderSpotsList(filter) {
  spotsFilter = filter;
  document.querySelectorAll('.sf-btn').forEach(b => b.classList.remove('sf-active'));
  const activeBtn = document.getElementById('sf-'+filter);
  if (activeBtn) activeBtn.classList.add('sf-active');

  const container = document.getElementById('spots-list');
  container.innerHTML = '';
  const cats = filter === 'all' ? SPOT_CATEGORIES : SPOT_CATEGORIES.filter(c => c.key === filter);
  let count = 0;
  cats.forEach(cat => {
    const spots = spotsData[cat.key] || [];
    if (!spots.length) return;
    const hdr = document.createElement('div');
    hdr.style.cssText = 'color:#7ee8a2;font-size:0.65rem;font-weight:bold;padding:5px 10px 3px;position:sticky;top:0;background:#1e2a4e;border-bottom:1px solid #2a2a4e;';
    hdr.textContent = cat.label + `（${spots.length}）`;
    container.appendChild(hdr);
    spots.forEach(p => {
      const row = document.createElement('div');
      row.style.cssText = 'padding:6px 10px;cursor:pointer;font-size:0.68rem;border-bottom:1px solid #1a2240;display:flex;justify-content:space-between;align-items:center;';
      row.innerHTML = `<span>${p.name}</span><span style="color:#555;font-size:0.6rem">${p.lat.toFixed(3)},${p.lng.toFixed(3)}</span>`;
      row.onmouseover = () => row.style.background='#2a3a6e';
      row.onmouseout  = () => row.style.background='';
      row.onclick = () => { closeSpotsModal(); flyToSpot(p.lat, p.lng, p.name, cat.type); };
      container.appendChild(row);
      count++;
    });
  });
  if (!count) container.innerHTML='<div style="color:#888;text-align:center;padding:20px;font-size:0.72rem">無資料</div>';
}

function loadAllSpotsAsMarkers() {
  if (!spotsData) return;
  let total = 0;
  SPOT_CATEGORIES.forEach(cat => {
    (spotsData[cat.key]||[]).forEach(p => { addCustomMarker(p.lat, p.lng, p.name, cat.type, false); total++; });
  });
  saveCustomMarkers();
  closeSpotsModal();
  document.getElementById('info-text').textContent = `✅ 已載入 ${total} 個熱點標記`;
}

// ── 初始化 ──
refreshRouteList();
loadCustomMarkers();
restoreRouteState();
// 開頁時檢查手機是否仍連線（補上非模擬狀態的還原）
(async()=>{
  if (phoneConnected) return;
  try {
    const s=await (await fetch('/phone_status')).json();
    if (s.connected) {
      phoneConnected=true;
      const btn=document.getElementById('btn-connect');
      btn.textContent='📱 已連線'; btn.style.background='#7ee8a2'; btn.style.color='#1a1a2e'; btn.disabled=false;
      updateUI();
    }
  } catch {}
})();
if (window.innerWidth<=640) {
  document.getElementById('route-content').classList.add('collapsed');
  document.getElementById('route-arrow').textContent='▸';
}

function toggleSidebar() {
  const sb = document.getElementById('sidebar');
  const btn = document.getElementById('btn-sb-toggle');
  const collapsed = sb.classList.toggle('sb-collapsed');
  btn.textContent = collapsed ? '⬆ 展開' : '⬇ 收起';
  setTimeout(() => map.invalidateSize(), 260);
}

// ── 疊圖輔助 ─────────────────────────────────────────────
let mapImageOverlay = null;
let overlayNWMarker = null;
let overlaySEMarker = null;
let overlayCenterMarker = null;
let overlayRotateHandle = null;
let overlayPickMode = false;
let overlayRotation = 0;
let overlayScale = 100;
let overlayBaseLatDiff = 0;
let overlayBaseLngDiff = 0;
let _prevPanPos = null;

function uploadMapImage(event) {
  const file = event.target.files[0];
  if (!file) return;
  const fd = new FormData();
  fd.append('file', file);
  fetch('/api/map_image', {method:'POST', body:fd})
    .then(r => r.json())
    .then(d => { if (d.url) showMapOverlay(d.url); })
    .catch(() => alert('上傳失敗'));
}

function showMapOverlay(url) {
  const b = map.getBounds();
  const nLat = b.getNorth(), sLat = b.getSouth();
  const wLng = b.getWest(), eLng = b.getEast();
  overlayBaseLatDiff = nLat - sLat;
  overlayBaseLngDiff = eLng - wLng;
  overlayScale = 100; overlayRotation = 0; _prevPanPos = null;
  if (mapImageOverlay) map.removeLayer(mapImageOverlay);
  mapImageOverlay = L.imageOverlay(url, [[nLat, wLng], [sLat, eLng]], {opacity:0.7, interactive:false}).addTo(map);
  const cIcon = L.divIcon({className:'', html:'<div class="overlay-corner"></div>', iconAnchor:[13,13]});
  const pIcon = L.divIcon({className:'', html:'<div style="width:22px;height:22px;background:#f0c040;border:2px solid #fff;border-radius:50%;cursor:move;display:flex;align-items:center;justify-content:center;font-size:13px;line-height:1">✛</div>', iconAnchor:[11,11]});
  if (overlayNWMarker) map.removeLayer(overlayNWMarker);
  if (overlaySEMarker) map.removeLayer(overlaySEMarker);
  if (overlayCenterMarker) map.removeLayer(overlayCenterMarker);
  overlayNWMarker = L.marker([nLat, wLng], {draggable:true, icon:cIcon, zIndexOffset:1000}).addTo(map);
  overlaySEMarker = L.marker([sLat, eLng], {draggable:true, icon:cIcon, zIndexOffset:1000}).addTo(map);
  overlayCenterMarker = L.marker([sLat, (wLng+eLng)/2], {draggable:true, icon:pIcon, zIndexOffset:1001}).addTo(map);
  const rIcon = L.divIcon({className:'', html:'<div style="width:28px;height:28px;background:#e06060;border:2px solid #fff;border-radius:50%;cursor:grab;display:flex;align-items:center;justify-content:center;font-size:16px;line-height:1">↻</div>', iconAnchor:[14,14]});
  if (overlayRotateHandle) map.removeLayer(overlayRotateHandle);
  overlayRotateHandle = L.marker([(nLat+sLat)/2, eLng], {draggable:true, icon:rIcon, zIndexOffset:1002}).addTo(map);
  overlayNWMarker.on('drag', _resizeFromCorners);
  overlaySEMarker.on('drag', _resizeFromCorners);
  overlayCenterMarker.on('dragstart', function() { _prevPanPos = this.getLatLng(); });
  overlayCenterMarker.on('drag', _panOverlay);
  overlayRotateHandle.on('drag', _rotateFromHandle);
  const _origReset = mapImageOverlay._reset.bind(mapImageOverlay);
  mapImageOverlay._reset = function() { _origReset(); requestAnimationFrame(_applyOverlayRotation); };
  map.on('zoomend', _applyOverlayRotation);
  document.getElementById('overlay-rotation').value = 0;
  document.getElementById('overlay-scale').value = 100;
  document.getElementById('overlay-controls').style.display = '';
}

function _overlayCenter() {
  const nw = overlayNWMarker.getLatLng(), se = overlaySEMarker.getLatLng();
  return {lat:(nw.lat+se.lat)/2, lng:(nw.lng+se.lng)/2, eLng:Math.max(nw.lng,se.lng), sLat:Math.min(nw.lat,se.lat)};
}

function _syncHandles() {
  const c = _overlayCenter();
  overlayCenterMarker.setLatLng([c.sLat, c.lng]);
  overlayRotateHandle.setLatLng([c.lat, c.eLng]);
}

function _resizeFromCorners() {
  if (!mapImageOverlay) return;
  const nw = overlayNWMarker.getLatLng(), se = overlaySEMarker.getLatLng();
  overlayBaseLatDiff = Math.abs(nw.lat - se.lat);
  overlayBaseLngDiff = Math.abs(se.lng - nw.lng);
  overlayScale = 100;
  document.getElementById('overlay-scale').value = 100;
  mapImageOverlay.setBounds([nw, se]);
  _syncHandles();
  _applyOverlayRotation();
}

function _rotateFromHandle() {
  const c = _overlayCenter();
  const centerPx = map.latLngToLayerPoint([c.lat, c.lng]);
  const hPx = map.latLngToLayerPoint(overlayRotateHandle.getLatLng());
  const deg = Math.round(Math.atan2(hPx.y - centerPx.y, hPx.x - centerPx.x) * 180 / Math.PI);
  overlayRotation = deg;
  const clamped = Math.max(-45, Math.min(45, deg));
  document.getElementById('overlay-rotation').value = clamped;
  _applyOverlayRotation();
}

function _panOverlay() {
  const newPos = overlayCenterMarker.getLatLng();
  if (!_prevPanPos) { _prevPanPos = newPos; return; }
  const dLat = newPos.lat - _prevPanPos.lat, dLng = newPos.lng - _prevPanPos.lng;
  const nw = overlayNWMarker.getLatLng(), se = overlaySEMarker.getLatLng();
  overlayNWMarker.setLatLng([nw.lat+dLat, nw.lng+dLng]);
  overlaySEMarker.setLatLng([se.lat+dLat, se.lng+dLng]);
  mapImageOverlay.setBounds([overlayNWMarker.getLatLng(), overlaySEMarker.getLatLng()]);
  _syncHandles();
  _prevPanPos = newPos;
  _applyOverlayRotation();
}

function setOverlayOpacity(v) {
  if (mapImageOverlay) mapImageOverlay.setOpacity(v / 100);
}

function setOverlayScale(pct) {
  overlayScale = parseInt(pct);
  if (!overlayNWMarker || !overlaySEMarker) return;
  const nw = overlayNWMarker.getLatLng(), se = overlaySEMarker.getLatLng();
  const cLat = (nw.lat+se.lat)/2, cLng = (nw.lng+se.lng)/2;
  const f = overlayScale/100;
  const dLat = overlayBaseLatDiff*f/2, dLng = overlayBaseLngDiff*f/2;
  const newNW = [cLat+dLat, cLng-dLng], newSE = [cLat-dLat, cLng+dLng];
  overlayNWMarker.setLatLng(newNW);
  overlaySEMarker.setLatLng(newSE);
  mapImageOverlay.setBounds([newNW, newSE]);
  _syncHandles();
  _applyOverlayRotation();
}

function adjustOverlayScale(delta, reset) {
  const s = document.getElementById('overlay-scale');
  s.value = reset ? 100 : Math.max(20, Math.min(300, parseInt(s.value)+delta));
  setOverlayScale(s.value);
}

function _applyOverlayRotation() {
  if (!mapImageOverlay) return;
  const el = mapImageOverlay.getElement();
  if (!el) return;
  el.style.imageRendering = '-webkit-optimize-contrast';
  el.style.willChange = 'transform';
  const pos = L.DomUtil.getPosition(el);
  el.style.transformOrigin = '50% 50%';
  el.style.transform = `translate3d(${pos.x}px,${pos.y}px,0)` +
    (overlayRotation ? ` rotate(${overlayRotation}deg)` : '');
}

function setOverlayRotation(deg) {
  overlayRotation = parseInt(deg);
  _applyOverlayRotation();
}

function adjustOverlayRotation(delta, reset) {
  const s = document.getElementById('overlay-rotation');
  s.value = reset ? 0 : Math.max(-45, Math.min(45, parseInt(s.value)+delta));
  setOverlayRotation(s.value);
}

function toggleOverlayPickMode() {
  overlayPickMode = !overlayPickMode;
  const btn = document.getElementById('btn-overlay-pick');
  btn.classList.toggle('overlay-active', overlayPickMode);
  btn.textContent = overlayPickMode ? '🎯 定位中（點地圖加點）' : '🎯 定位取點';
}

function removeMapOverlay() {
  [mapImageOverlay, overlayNWMarker, overlaySEMarker, overlayCenterMarker, overlayRotateHandle].forEach(l => { if(l) map.removeLayer(l); });
  mapImageOverlay = overlayNWMarker = overlaySEMarker = overlayCenterMarker = overlayRotateHandle = null;
  map.off('zoomend', _applyOverlayRotation);
  overlayPickMode = false; overlayRotation = 0; overlayScale = 100; _prevPanPos = null;
  document.getElementById('overlay-controls').style.display = 'none';
  document.getElementById('overlay-file').value = '';
  document.getElementById('overlay-rotation').value = 0;
  document.getElementById('overlay-scale').value = 100;
  const btn = document.getElementById('btn-overlay-pick');
  btn.classList.remove('overlay-active');
  btn.textContent = '🎯 定位取點';
}
</script>


<!-- 從標記選點 Modal -->
<div id="pickmarkers-overlay" onclick="closePickMarkersModal()"
     style="display:none;position:fixed;inset:0;background:#0007;z-index:9998"></div>
<div id="pickmarkers-modal"
     style="display:none;position:fixed;top:50%;left:50%;transform:translate(-50%,-50%);
            background:#1e2a4e;border:1px solid #3a3a6e;border-radius:10px;padding:14px;
            z-index:9999;width:320px;max-height:80vh;box-shadow:0 8px 24px #000c;
            flex-direction:column;gap:8px">
  <div style="display:flex;align-items:center;justify-content:space-between">
    <span style="color:#7ee8a2;font-weight:bold;font-size:0.8rem">📌 選擇尋菇點</span>
    <button onclick="closePickMarkersModal()" style="background:none;border:none;color:#888;cursor:pointer;font-size:1rem">✕</button>
  </div>
  <div style="font-size:0.62rem;color:#888">勾選要加入巡邏的標記，按確定後加為中繼點</div>
  <div style="display:flex;gap:4px;flex-wrap:wrap">
    <button class="sf-btn sf-active" id="pm-all"     onclick="renderPickList('all')">全部</button>
    <button class="sf-btn" id="pm-mushroom" onclick="renderPickList('mushroom')">🍄 蘑菇</button>
    <button class="sf-btn" id="pm-plant"    onclick="renderPickList('plant')">🌸 大花</button>
    <button class="sf-btn" id="pm-special"  onclick="renderPickList('special')">⭐ 明信片</button>
    <button class="sf-btn" id="pm-pin"      onclick="renderPickList('pin')">📍 標記</button>
  </div>
  <div id="pm-list" style="overflow-y:auto;max-height:300px;border:1px solid #2a2a4e;border-radius:6px;background:#131d35"></div>
  <div style="display:flex;gap:6px">
    <button onclick="confirmPickMarkers()"
            style="flex:1;background:#7ee8a2;color:#1a1a2e;border:none;border-radius:5px;padding:6px;cursor:pointer;font-size:0.65rem;font-weight:bold">
      ✓ 加為中繼點
    </button>
    <button onclick="closePickMarkersModal()"
            style="flex:1;background:#4a4a6a;color:#ccc;border:none;border-radius:5px;padding:6px;cursor:pointer;font-size:0.65rem">
      取消
    </button>
  </div>
</div>

<!-- 我的標記清單 Modal -->
<div id="mymarkers-overlay" onclick="closeMarkersModal()"
     style="display:none;position:fixed;inset:0;background:#0007;z-index:9998"></div>
<div id="mymarkers-modal"
     style="display:none;position:fixed;top:50%;left:50%;transform:translate(-50%,-50%);
            background:#1e2a4e;border:1px solid #3a3a6e;border-radius:10px;padding:14px;
            z-index:9999;width:320px;max-height:80vh;box-shadow:0 8px 24px #000c;
            flex-direction:column;gap:8px">
  <div style="display:flex;align-items:center;justify-content:space-between">
    <span style="color:#7ee8a2;font-weight:bold;font-size:0.8rem">📋 我的標記</span>
    <button onclick="closeMarkersModal()" style="background:none;border:none;color:#888;cursor:pointer;font-size:1rem;line-height:1">✕</button>
  </div>
  <div style="display:flex;gap:4px;flex-wrap:wrap">
    <button id="mm-all"      class="sf-btn sf-active" onclick="renderMarkersList('all')">全部</button>
    <button id="mm-mushroom" class="sf-btn" onclick="renderMarkersList('mushroom')">🍄 蘑菇</button>
    <button id="mm-plant"    class="sf-btn" onclick="renderMarkersList('plant')">🌸 大花</button>
    <button id="mm-special"  class="sf-btn" onclick="renderMarkersList('special')">⭐ 明信片</button>
    <button id="mm-pin"      class="sf-btn" onclick="renderMarkersList('pin')">📍 標記</button>
  </div>
  <div id="mm-list" style="overflow-y:auto;max-height:360px;border:1px solid #2a2a4e;border-radius:6px;background:#131d35"></div>
  <button onclick="closeMarkersModal()"
          style="background:#4a4a6a;color:#ccc;border:none;border-radius:5px;padding:6px;cursor:pointer;font-size:0.65rem;width:100%">
    關閉
  </button>
</div>

<!-- 熱點清單 Modal -->
<div id="spots-overlay" onclick="closeSpotsModal()"
     style="display:none;position:fixed;inset:0;background:#0007;z-index:9998"></div>
<div id="spots-modal"
     style="display:none;position:fixed;top:50%;left:50%;transform:translate(-50%,-50%);
            background:#1e2a4e;border:1px solid #3a3a6e;border-radius:10px;padding:14px;
            z-index:9999;width:320px;max-height:80vh;box-shadow:0 8px 24px #000c;
            flex-direction:column;gap:8px">
  <div style="display:flex;align-items:center;justify-content:space-between">
    <span style="color:#7ee8a2;font-weight:bold;font-size:0.8rem">🗺️ 遊戲熱點</span>
    <button onclick="closeSpotsModal()" style="background:none;border:none;color:#888;cursor:pointer;font-size:1rem;line-height:1">✕</button>
  </div>
  <div style="display:flex;gap:4px;flex-wrap:wrap">
    <button id="sf-all"        class="sf-btn sf-active" onclick="renderSpotsList('all')">全部</button>
    <button id="sf-mushrooms"  class="sf-btn" onclick="renderSpotsList('mushrooms')">🍄 蘑菇</button>
    <button id="sf-big_flowers"class="sf-btn" onclick="renderSpotsList('big_flowers')">🌸 大花</button>
    <button id="sf-postcards"  class="sf-btn" onclick="renderSpotsList('postcards')">⭐ 明信片</button>
    <button id="sf-taiwan_poi" class="sf-btn" onclick="renderSpotsList('taiwan_poi')">📍 台灣</button>
  </div>
  <div id="spots-list" style="overflow-y:auto;max-height:340px;border:1px solid #2a2a4e;border-radius:6px;background:#131d35"></div>
  <div style="display:flex;gap:6px;padding-top:4px;border-top:1px solid #2a2a4e">
    <button onclick="loadAllSpotsAsMarkers()"
            style="flex:1;background:#e879a0;color:#fff;border:none;border-radius:5px;padding:6px;cursor:pointer;font-size:0.65rem;font-weight:bold">
      📌 全部載入為標記
    </button>
    <button onclick="closeSpotsModal()"
            style="flex:1;background:#4a4a6a;color:#ccc;border:none;border-radius:5px;padding:6px;cursor:pointer;font-size:0.65rem">
      關閉
    </button>
  </div>
</div>
<div id="setup-overlay">
  <div id="setup-box">
    <h3>📱 新手機設定精靈</h3>
    <div id="setup-steps">
      <div class="setup-step" id="ss0">
        <div class="step-icon">①</div>
        <div class="step-text"><div class="step-title">連接手機</div><div class="step-desc">USB 線連接 iPhone 與本機</div></div>
      </div>
      <div class="setup-step" id="ss1">
        <div class="step-icon">②</div>
        <div class="step-text"><div class="step-title">信任此電腦</div><div class="step-desc">iPhone 螢幕點「信任」並輸入密碼</div></div>
      </div>
      <div class="setup-step" id="ss2">
        <div class="step-icon">③</div>
        <div class="step-text"><div class="step-title">開啟開發者模式</div><div class="step-desc">設定 → 隱私權與安全性 → 開發者模式</div></div>
      </div>
      <div class="setup-step" id="ss3">
        <div class="step-icon">④</div>
        <div class="step-text"><div class="step-title">安裝開發工具</div><div class="step-desc">自動掛載 DeveloperDiskImage</div></div>
      </div>
    </div>
    <div id="setup-progress-bar"><div id="setup-progress-fill"></div></div>
    <div id="setup-msg">偵測手機狀態中...</div>
    <button id="setup-action-btn" onclick="setupAction()" disabled>請稍候</button>
  </div>
</div>

<!-- ── 說明手冊 Modal ── -->
<div id="help-overlay" onclick="if(event.target===this)closeHelp()">
  <div id="help-box">
    <div id="help-hdr">
      <span>📖 GPsikmin 功能說明</span>
      <button onclick="closeHelp()">✕</button>
    </div>
    <div id="help-body">

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h0','ha0')">🚀 快速上手 <span id="ha0">▸</span></button>
        <div class="hs-body open" id="h0">
          <ul>
            <li>iPhone USB 接皮皮盒 → 連上 WiFi → 開啟 <b>http://192.168.4.1:5000</b> → 點 <b>🔌 連線手機</b></li>
            <li>在地圖上依序點選路線中繼點（至少 2 點）</li>
            <li>點 <b>▶ 開始</b>，🌱 標記開始沿路線移動</li>
            <li>點 <b>⏹ 停止</b> 隨時中斷</li>
          </ul>
          <div class="tip">連線時 iPhone 螢幕必須亮著（解鎖狀態），建立 tunnel 約需 5–35 秒</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h1','ha1')">⚙️ 基本控制 <span id="ha1">▸</span></button>
        <div class="hs-body" id="h1">
          <ul>
            <li><b>速度滑桿</b>：3–25 km/h，每步自動 ±15% 隨機化，並加入隨機停頓，模擬真人步伐</li>
            <li><b>跟隨</b>：地圖自動跟著目前位置移動（可關閉手動拖地圖）</li>
            <li><b>↩ 上一點</b>：刪除最後一個中繼點並重算路線</li>
            <li><b>🗑 清除</b>：清除所有中繼點與路線</li>
            <li><b>暖機警告</b>：新起點距上次停止點 &gt;500m 時，跳出確認提示</li>
          </ul>
          <div class="tip">📱 手機版：標題列右側有「⬇ 收起」按鈕，收起工具列後地圖全螢幕；再按「⬆ 展開」恢復</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h2','ha2')">🗺️ 行走模式 <span id="ha2">▸</span></button>
        <div class="hs-body" id="h2">
          <table>
            <tr><td>模式</td><td>說明</td></tr>
            <tr><td><b>一般</b>（預設）</td><td>OSRM 走真實街道，沿規劃路徑移動</td></tr>
            <tr><td><b>折返</b></td><td>跑到終點後反向重跑，無限循環；畫面顯示圈數與累計公里數</td></tr>
            <tr><td><b>直線</b></td><td>中繼點間走直線（黃色虛線），可穿越公園、無道路區域</td></tr>
          </table>
          <div class="tip">直線模式適合在公園內定點或特殊地形，不受道路限制</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h3','ha3')">🍄 尋菇模式 <span id="ha3">▸</span></button>
        <div class="hs-body" id="h3">
          <ul>
            <li>勾選「🍄 尋菇模式」後，▶ 開始變為「🍄 開始尋菇」</li>
            <li>依序在每個中繼點<b>停留 N 分鐘</b>（預設 5 分鐘），每 2 秒送一次帶漂移的座標</li>
            <li>狀態列顯示「第 X/N 點 M:SS」倒數 + 進度條</li>
            <li>勾選「<b>循環</b>」→ 跑完全部點自動重頭，狀態列顯示第 N 圈</li>
            <li>按「<b>📌 從標記選點</b>」→ 從已存的地圖標記中挑選目標點（可篩類型）</li>
          </ul>
          <div class="tip">尋菇模式完全獨立，不影響一般行走路線設定</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h4','ha4')">🌸 瞬間移動 <span id="ha4">▸</span></button>
        <div class="hs-body" id="h4">
          <ul>
            <li>勾選「🌸 瞬間移動」後設定<b>目標座標</b>（或點「📍 地圖中心」自動填入）</li>
            <li>按「✓ 確認座標」在地圖上標記目標點</li>
            <li>按 ▶ 開始後，先從 5m 外慢慢走到目標點，然後<b>停在目標定點</b>持續微漂移</li>
            <li>手動按 ⏹ 停止離開</li>
            <li>適合在固定地點種花（大花/路邊花），不需要設路線中繼點</li>
          </ul>
          <div class="tip">微漂移會模擬 GPS 自然抖動（±4m），避免被遊戲判定為定位凍結</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h5','ha5')">🚶 繞圈種花 <span id="ha5">▸</span></button>
        <div class="hs-body" id="h5">
          <ul>
            <li>勾選「🚶 繞圈種花」後設定<b>圓心座標</b>（或點「📍 地圖中心」）</li>
            <li>按「✓ 確認座標」在地圖上標記圓心與圓圈</li>
            <li>調整<b>半徑</b>（10–50m，滑桿控制），圓圈即時更新</li>
            <li>按 ▶ 開始後，依速度設定持續繞圓移動，不需設路線中繼點</li>
            <li>手動按 ⏹ 停止離開</li>
            <li>適合在大花 / 目標點外圍繞行種花</li>
          </ul>
          <div class="tip">繞圈會加入 GPS 漂移，不會走出完美圓形，降低被偵測風險</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h6','ha6')">📍 地圖標記 <span id="ha6">▸</span></button>
        <div class="hs-body" id="h6">
          <ul>
            <li>點 🍄🌸⭐📍 其中一個按鈕進入標記模式，再點地圖選位置並輸入名稱</li>
            <li>再次點同一個按鈕，或按 Esc 退出標記模式</li>
            <li>標記儲存在伺服器（<code>static/markers.json</code>），換裝置也看得到</li>
            <li>點「<b>📋 我的標記</b>」開啟清單，可按類型篩選、點擊定位、刪除標記</li>
          </ul>
          <table>
            <tr><td>圖示</td><td>用途</td></tr>
            <tr><td>🍄</td><td>蘑菇位置</td></tr>
            <tr><td>🌸</td><td>大花位置</td></tr>
            <tr><td>⭐</td><td>明信片 / 特殊地點</td></tr>
            <tr><td>📍</td><td>一般自訂標記</td></tr>
          </table>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h13','ha13')">🗾 疊圖輔助 <span id="ha13">▸</span></button>
        <div class="hs-body" id="h13">
          <ul>
            <li>把遊戲截圖疊在地圖上，協助對準 GPS 位置（標點或設路線用）</li>
            <li>先把地圖移到截圖對應的區域，展開側欄「🗾 疊圖輔助」→ 點「📸 上傳遊戲截圖」</li>
            <li>截圖出現後，拖曳地圖上的三個把手調整位置：</li>
          </ul>
          <table>
            <tr><td>把手</td><td>功能</td></tr>
            <tr><td>🟢 角點</td><td>拖曳縮放截圖大小</td></tr>
            <tr><td>🟡 底部</td><td>拖曳平移截圖位置</td></tr>
            <tr><td>🔴 右側</td><td>拖曳旋轉截圖角度</td></tr>
          </table>
          <ul>
            <li><b>透明度</b>滑桿：調整截圖透明度，方便和地圖對照</li>
            <li><b>🎯 定位取點</b>：開啟後點地圖，在截圖對準位置直接加入路線中繼點</li>
            <li><b>🗑 移除</b>：移除截圖疊圖</li>
          </ul>
          <div class="tip">對準技巧：先用 🟡 把手平移到大致位置，再用 🟢 縮放比例，最後用 🔴 微調角度</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h7','ha7')">📁 路線管理 <span id="ha7">▸</span></button>
        <div class="hs-body" id="h7">
          <ul>
            <li><b>儲存</b>：輸入路線名稱 → 💾 儲存（含中繼點 + 完整路線座標）</li>
            <li><b>載入</b>：下拉選擇路線 → 📂 載入，自動還原地圖路線</li>
            <li><b>熱點</b>：🗺️ 熱點，開啟 pogoskill 台灣蘑菇/大花/明信片/POI 清單，點擊定位或載入為標記</li>
            <li><b>刪除</b>：選擇路線 → 🗑</li>
            <li><b>匯出</b>：⬇ 匯出，將選取路線加密下載為 <code>.gpsikmin</code> 檔（僅皮皮盒可讀取）</li>
            <li><b>匯入</b>：⬆ 匯入，選擇 <code>.gpsikmin</code> 加密路線或 <code>.json</code> 明文路線，匯入後自動加入下拉清單</li>
            <li><b>GPX 匯入</b>：📁 GPX，選擇 .gpx 檔案，trackpoint 作路線、waypoint 走 OSRM</li>
          </ul>
          <div class="tip">路線檔存在 Pi 的 <code>routes/</code> 目錄，路線名稱建議取有意義的名字方便辨識</div>
          <div class="tip">⬇ 匯出的 .gpsikmin 為加密格式，只有同一把金鑰的皮皮盒才能匯入，非本機裝置匯入會被拒絕</div>
        </div>
      </div>


      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h9','ha9')">🌙 掛機模式 <span id="ha9">▸</span></button>
        <div class="hs-body" id="h9">
          <ul>
            <li>開啟後按鈕變紫色，進入掛機狀態</li>
            <li>若偵測到手機斷線，自動重新連線並重啟模擬</li>
            <li>支援所有模式：行走、尋菇、瞬間移動、繞圈種花</li>
            <li>適合放著跑一整晚、不需守著螢幕</li>
          </ul>
          <div class="tip">掛機模式跑在瀏覽器前端，關閉分頁會失效。建議把瀏覽器分頁固定（Pin Tab）避免誤關</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h12','ha12')">🕹️ 實體搖桿 <span id="ha12">▸</span></button>
        <div class="hs-body" id="h12">
          <ul>
            <li>搖桿開機後會自動連上皮皮盒，● 指示燈變綠表示已連線</li>
            <li>按「🕹️ 搖桿 ●」按鈕進入搖桿模式</li>
            <li><b>粗調</b>：撥一下立即跳躍固定距離（不管搖桿停留多久），可選 50 / 100 / 200 / 500 m</li>
            <li><b>微調</b>：持續按住方向，按照速度滑桿設定的速度連續移動</li>
            <li>按 <b>[粗調] / [微調]</b> 切換模式；粗調模式下可再選跳距</li>
            <li>搖桿中間按鍵<b>長按 1.5 秒</b>＝ 完全停止（防誤觸）</li>
          </ul>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h14','ha14')">👟 自動加步數 <span id="ha14">▸</span></button>
        <div class="hs-body" id="h14">
          <p>模擬行走時自動累計步數（每公里約 1300 步），透過 iOS 捷徑自動寫入 HealthKit。</p>
          <b>安全限制</b>
          <ul>
            <li>每次最多領取 <b>5,000 步</b>，模擬正常走路節奏</li>
            <li>每日上限 <b>50,000 步</b>，超過自動停止（避免被 Niantic 偵測）</li>
            <li>每天午夜自動重置額度</li>
            <li>超過的步數會保留，下次自動化執行時繼續領取</li>
          </ul>
          <b>原理</b>
          <ul>
            <li>HealthKit 接受任何有權限的 App 寫入步數</li>
            <li>Pikmin Bloom 讀取 HealthKit <b>所有來源</b>的步數，不區分手動或感應器</li>
          </ul>
          <b>建立捷徑（只需做一次）</b>
          <ul>
            <li>開啟「捷徑」App → <b>＋</b> → 加入動作 →<b>「取得URL的內容」</b></li>
            <li>網址輸入 <b>http://192.168.4.1:5000/api/steps</b></li>
            <li>再加動作 →<b>「紀錄健康樣本」</b>→ 類型選<b>步數</b>，數值選<b>「URL 的內容」</b></li>
            <li>改名為「加步數」→ 完成</li>
          </ul>
          <b>設定自動執行</b>
          <ul>
            <li>「自動化」頁籤 → <b>＋</b> →「每天的特定時間」→ 分別建 <b>08:00、12:00、18:00、22:00</b> 四個</li>
            <li>每個都選動作「執行捷徑」→「加步數」→ 關閉「執行前先詢問」</li>
          </ul>
          <b>前置設定</b>
          <ul>
            <li>設定 → 健康 → 資料權限與裝置 → 捷徑 → 允許寫入<b>「步行」</b></li>
          </ul>
          <div class="tip">手機連著皮皮盒 WiFi 時，捷徑會在背景自動執行。側欄面板可看「今日已寫入」進度。</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h10','ha10')">🔍 搜尋與定位 <span id="ha10">▸</span></button>
        <div class="hs-body" id="h10">
          <ul>
            <li><b>搜尋框</b>：輸入中文地址或地名 → 按搜尋 → 點結果飛到該地</li>
            <li><b>GPS 跳轉框</b>（地圖左下角）：輸入「緯度,經度」或按 Enter 直接飛到座標</li>
            <li>飛到後地圖顯示<b>紅色十字準星</b>，可點 popup「加為中繼點」或「移除」</li>
          </ul>
          <div class="tip">座標格式範例：<code>25.0478,121.5319</code>（台北 101）</div>
        </div>
      </div>

      <div class="hs">
        <button class="hs-btn" onclick="toggleHs('h11','ha11')">📱 首次設定新手機 <span id="ha11">▸</span></button>
        <div class="hs-body" id="h11">
          <ul>
            <li>同一支手機只需設定一次，之後插上即可直接連線</li>
          </ul>
          <table>
            <tr><td>步驟</td><td>操作</td></tr>
            <tr><td>① 信任</td><td>iPhone 螢幕點「信任此電腦」</td></tr>
            <tr><td>② 配對</td><td>Pi 自動執行配對</td></tr>
            <tr><td>③ 開發者模式</td><td>iPhone 設定 → 隱私權與安全性 → 開發者模式 → 開啟 → 重開機</td></tr>
            <tr><td>④ 重開機後</td><td>輸入數字 PIN 碼（不能用 Face ID），Pi 才能偵測到</td></tr>
            <tr><td>⑤ 掛載</td><td>Pi 自動掛載 DeveloperDiskImage</td></tr>
          </table>
        </div>
      </div>

    </div>
  </div>
</div>

<div id="goldpot-overlay" style="display:none;position:fixed;top:0;left:0;width:100%;height:100%;
  background:rgba(0,0,0,0.9);z-index:9999;align-items:center;justify-content:center;flex-direction:column;gap:14px">
  <div style="font-size:4rem">🪣</div>
  <div id="goldpot-title" style="font-size:1.8rem;color:#FFD700;font-weight:bold;text-align:center;padding:0 20px">凍結GPS中，準備互動</div>
  <div id="goldpot-sub" style="color:#aaa;font-size:0.95rem;text-align:center;padding:0 20px">切換到 Pikmin Bloom，倒數結束後立刻互動金盆</div>
  <div id="goldpot-timer" style="font-size:4rem;color:#fff;font-weight:bold;min-width:60px;text-align:center"></div>
  <button onclick="document.getElementById('goldpot-overlay').style.display='none'"
    style="padding:10px 28px;font-size:1rem;background:#555;color:#fff;border:none;border-radius:8px;cursor:pointer;margin-top:8px">
    關閉
  </button>
</div>

</body>
</html>
"""


PMD3 = "/home/pikmin/.local/bin/pymobiledevice3"


def check_iphone():
    try:
        result = subprocess.run(["ideviceinfo", "-k", "UniqueDeviceID"],
                                capture_output=True, text=True, timeout=5)
        return result.returncode == 0 and len(result.stdout.strip()) >= 20
    except Exception:
        return False


def fix_dns():
    try:
        socket.setdefaulttimeout(3)
        socket.getaddrinfo("tile.openstreetmap.org", 80)
        return True
    except OSError:
        pass
    print("  🔧 DNS 失效，自動修復中...")
    os.system("sudo tailscale set --accept-dns=false 2>/dev/null")
    os.system("sudo bash -c 'echo nameserver 8.8.8.8 > /etc/resolv.conf'")
    try:
        socket.getaddrinfo("tile.openstreetmap.org", 80)
        print("  ✅ DNS 已修復")
        return True
    except OSError:
        print("  ⚠  DNS 修復失敗，地圖磚片可能無法顯示")
        return False


def ensure_tunneld():
    global _tunneld_starting
    try:
        r = requests.get(TUNNELD_URL, timeout=2)
        if r.json():
            print("  ✅ tunneld 已在執行中且有裝置")
            return None
        print("  🔄 tunneld 無裝置，重新啟動...")
        os.system("sudo pkill -f 'pymobiledevice3 remote tunneld' 2>/dev/null")
        time.sleep(2)
    except Exception:
        pass
    print("  🔧 啟動 tunneld（需要管理員權限）...")
    _tunneld_starting = True
    try:
        env = os.environ.copy()
        env["PYTHONPATH"] = str(pathlib.Path.home() / ".local/lib" / f"python{sys.version_info.major}.{sys.version_info.minor}/site-packages")
        env["PATH"] = f"{pathlib.Path.home() / '.local/bin'}:/usr/local/bin:/usr/bin:/bin"
        proc = subprocess.Popen(
            ["sudo", "-E", sys.executable, "-m", "pymobiledevice3", "remote", "tunneld"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env
        )
        print("  ⏳ 等待 iPhone tunnel 建立（請確認手機已解鎖）", end="", flush=True)
        for _ in range(35):
            time.sleep(1)
            print(".", end="", flush=True)
            try:
                r = requests.get(TUNNELD_URL, timeout=1)
                if r.json():
                    print(" 就緒！")
                    return proc
            except Exception:
                pass
        print(" 逾時")
        print("  ⚠  請確認：1) iPhone 已解鎖  2) USB 線接好  3) 已信任此電腦")
        return proc
    finally:
        _tunneld_starting = False


def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "localhost"


if __name__ == "__main__":
    print("\n" + "=" * 52)
    print("  🌱  GPsikmin 啟動中...")
    print("=" * 52)

    fix_dns()

    def cleanup(sig=None, frame=None):
        print("\n\n🛑 關閉中...")
        stop_flag.set()
        if tunneld_proc:
            os.system(f"sudo kill {tunneld_proc.pid} 2>/dev/null")
        sys.exit(0)

    signal.signal(signal.SIGINT, cleanup)
    signal.signal(signal.SIGTERM, cleanup)

    local_ip = get_local_ip()
    print("\n" + "=" * 52)
    print(f"  ✅ 就緒！v{VERSION}")
    print(f"  AP 模式： http://192.168.4.1:5000")
    print(f"  同網段：  http://{local_ip}:5000")
    print("=" * 52)
    print("  按 Ctrl+C 結束\n")

    app.run(host="0.0.0.0", port=5000, debug=False, threaded=True, use_reloader=False)
