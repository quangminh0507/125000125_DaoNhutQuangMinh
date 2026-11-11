"""Đề 17 - Mô phỏng lịch trình xe buýt (Python + Tkinter).

Chạy giao diện: python main.py
Chạy kiểm thử: python main.py --test
Đo hiệu năng:   python main.py --benchmark

Chỉ cần file này và Python 3.10+ (Tkinter là thư viện chuẩn).
Dữ liệu mẫu gồm 25 trạm, 8 tuyến, mỗi tuyến đi hai chiều.
"""

from __future__ import annotations

import csv
import gc
import heapq
import io
import random
import sys
import threading
import tracemalloc
import unittest
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from queue import Empty, Queue
from statistics import mean
from time import perf_counter


# ============================================================
# 1. CẤU TRÚC DỮ LIỆU: ĐỒ THỊ DẠNG DANH SÁCH KỀ
# ============================================================


def chuan_hoa_ma(ma: str) -> str:
    if not isinstance(ma, str) or not ma.strip():
        raise ValueError("Mã trạm hoặc tuyến không được để trống.")
    return ma.strip().upper()


class TransitGraph:
    """Mỗi trạm là một đỉnh; mỗi đoạn giữa hai trạm kề là một cạnh có mã tuyến."""

    def __init__(self) -> None:
        self.stops: dict[str, str] = {}            # Mã trạm -> tên trạm
        self.routes: dict[str, tuple[str, ...]] = {}  # Mã tuyến -> các trạm theo thứ tự
        self.adjacency: dict[str, list[tuple[str, str]]] = {}  # Trạm -> (trạm kề, tuyến)

    def add_stop(self, ma_tram: str, ten_tram: str) -> None:
        ma_tram = chuan_hoa_ma(ma_tram)
        if not isinstance(ten_tram, str) or not ten_tram.strip():
            raise ValueError("Tên trạm không được để trống.")
        if ma_tram in self.stops:
            raise ValueError(f"Trạm {ma_tram} đã tồn tại.")
        self.stops[ma_tram] = ten_tram.strip()
        self.adjacency[ma_tram] = []

    def add_route(self, ma_tuyen: str, danh_sach_tram) -> None:
        ma_tuyen = chuan_hoa_ma(ma_tuyen)
        if ma_tuyen in self.routes:
            raise ValueError(f"Tuyến {ma_tuyen} đã tồn tại.")
        if danh_sach_tram is None:
            raise ValueError("Tuyến phải có ít nhất 2 trạm.")
        tram = [chuan_hoa_ma(ma) for ma in danh_sach_tram]
        if len(tram) < 2:
            raise ValueError("Tuyến phải có ít nhất 2 trạm.")
        if len(set(tram)) != len(tram):
            raise ValueError("Một tuyến không được lặp trạm trong dữ liệu mẫu.")
        for ma in tram:
            if ma not in self.stops:
                raise ValueError(f"Trạm {ma} chưa được khai báo.")

        self.routes[ma_tuyen] = tuple(tram)
        for a, b in zip(tram, tram[1:]):
            self.adjacency[a].append((b, ma_tuyen))
            self.adjacency[b].append((a, ma_tuyen))  # Dữ liệu mô phỏng đi hai chiều

    def has_stop(self, ma_tram: str) -> bool:
        return isinstance(ma_tram, str) and ma_tram.strip().upper() in self.stops

    def neighbors(self, ma_tram: str) -> list[tuple[str, str]]:
        return self.adjacency[ma_tram]


@dataclass(frozen=True)
class Segment:
    tu_tram: str
    den_tram: str
    ma_tuyen: str


@dataclass(frozen=True)
class Journey:
    bat_dau: str
    ket_thuc: str
    segments: tuple[Segment, ...]

    @property
    def so_doan(self) -> int:
        return len(self.segments)

    @property
    def so_lan_chuyen_tuyen(self) -> int:
        return sum(
            self.segments[i].ma_tuyen != self.segments[i - 1].ma_tuyen
            for i in range(1, len(self.segments))
        )


def create_demo_graph() -> TransitGraph:
    """Bộ dữ liệu đúng đề số 17: 8 tuyến, 25 trạm."""
    graph = TransitGraph()
    ten_tram = [
        "Bến xe trung tâm", "Công viên A", "Chợ thành phố",
        "Bệnh viện", "Đại học", "Bến xe phía Bắc",
        "Nhà văn hóa", "Siêu thị", "Ga đường sắt",
        "Khu công nghiệp", "Trường THPT", "Bảo tàng",
        "Sân vận động", "Bến xe phía Nam", "Ký túc xá",
        "Thư viện", "Chợ phía Tây", "Trung tâm thể thao",
        "Công viên B", "Nhà hát", "Trung tâm hành chính",
        "Bưu điện", "Chợ phía Đông", "Trung tâm thương mại",
        "Bến xe phía Đông",
    ]
    for i, ten in enumerate(ten_tram, start=1):
        graph.add_stop(f"S{i:02d}", ten)

    cac_tuyen = {
        "T01": ["S01", "S02", "S03", "S04", "S05", "S06"],
        "T02": ["S04", "S07", "S08", "S09", "S10"],
        "T03": ["S09", "S11", "S12", "S13", "S14"],
        "T04": ["S03", "S15", "S16", "S17"],
        "T05": ["S16", "S18", "S19", "S20"],
        "T06": ["S06", "S21", "S22", "S23"],
        "T07": ["S20", "S24", "S25", "S14"],
        "T08": ["S08", "S18", "S22", "S25"],
    }
    for ma_tuyen, cac_tram in cac_tuyen.items():
        graph.add_route(ma_tuyen, cac_tram)
    return graph


# ============================================================
# 2. THUẬT TOÁN TÌM ĐƯỜNG
# ============================================================


def kiem_tra_tram(graph: TransitGraph, bat_dau: str, ket_thuc: str) -> tuple[str, str]:
    bat_dau = chuan_hoa_ma(bat_dau)
    ket_thuc = chuan_hoa_ma(ket_thuc)
    if not graph.has_stop(bat_dau) or not graph.has_stop(ket_thuc):
        raise ValueError("Trạm xuất phát hoặc trạm đích không tồn tại.")
    return bat_dau, ket_thuc


def _tao_hanh_trinh_bfs(bat_dau: str, ket_thuc: str, cha: dict) -> Journey:
    cac_doan = []
    hien_tai = ket_thuc
    while hien_tai != bat_dau:
        tram_truoc, ma_tuyen = cha[hien_tai]
        cac_doan.append(Segment(tram_truoc, hien_tai, ma_tuyen))
        hien_tai = tram_truoc
    cac_doan.reverse()
    return Journey(bat_dau, ket_thuc, tuple(cac_doan))


def find_shortest_by_stops(graph: TransitGraph, bat_dau: str, ket_thuc: str) -> Journey | None:
    """BFS: tối ưu số đoạn trạm; độ phức tạp O(V + E)."""
    bat_dau, ket_thuc = kiem_tra_tram(graph, bat_dau, ket_thuc)
    if bat_dau == ket_thuc:
        return Journey(bat_dau, ket_thuc, ())

    hang_doi = deque([bat_dau])
    da_tham = {bat_dau}
    cha = {}  # Trạm -> (trạm trước, tuyến đang dùng)
    while hang_doi:
        hien_tai = hang_doi.popleft()
        for tram_ke, ma_tuyen in graph.neighbors(hien_tai):
            if tram_ke in da_tham:
                continue
            da_tham.add(tram_ke)
            cha[tram_ke] = (hien_tai, ma_tuyen)
            if tram_ke == ket_thuc:
                return _tao_hanh_trinh_bfs(bat_dau, ket_thuc, cha)
            hang_doi.append(tram_ke)
    return None


def _tao_hanh_trinh_chuyen_tuyen(
    bat_dau: str, ket_thuc: str, dich: tuple, nguon: tuple, cha: dict
) -> Journey:
    cac_doan = []
    hien_tai = dich
    while hien_tai != nguon:
        tram_truoc, tuyen_truoc = cha[hien_tai]
        cac_doan.append(Segment(tram_truoc, hien_tai[0], hien_tai[1]))
        hien_tai = (tram_truoc, tuyen_truoc)
    cac_doan.reverse()
    return Journey(bat_dau, ket_thuc, tuple(cac_doan))


def find_fewest_transfers(graph: TransitGraph, bat_dau: str, ket_thuc: str) -> Journey | None:
    """0-1 BFS: đi cùng tuyến giá 0, chuyển tuyến giá 1.

    Trạng thái (trạm, tuyến hiện tại); lên tuyến đầu tiên không tính là chuyển.
    Tối ưu số lần đổi tuyến, không đảm bảo ít đoạn nhất nếu nhiều phương án đồng hạng.
    """
    bat_dau, ket_thuc = kiem_tra_tram(graph, bat_dau, ket_thuc)
    if bat_dau == ket_thuc:
        return Journey(bat_dau, ket_thuc, ())

    nguon = (bat_dau, None)
    hang_doi = deque([(nguon, 0)])
    khoang_cach = {nguon: 0}
    cha = {}
    while hang_doi:
        (tram, tuyen_dang_di), chi_phi = hang_doi.popleft()
        if chi_phi != khoang_cach[(tram, tuyen_dang_di)]:
            continue
        if tram == ket_thuc:
            return _tao_hanh_trinh_chuyen_tuyen(
                bat_dau, ket_thuc, (tram, tuyen_dang_di), nguon, cha
            )
        for tram_ke, tuyen_moi in graph.neighbors(tram):
            doi_tuyen = int(tuyen_dang_di is not None and tuyen_dang_di != tuyen_moi)
            chi_phi_moi = chi_phi + doi_tuyen
            trang_thai_moi = (tram_ke, tuyen_moi)
            if chi_phi_moi < khoang_cach.get(trang_thai_moi, float("inf")):
                khoang_cach[trang_thai_moi] = chi_phi_moi
                cha[trang_thai_moi] = (tram, tuyen_dang_di)
                if doi_tuyen == 0:
                    hang_doi.appendleft((trang_thai_moi, chi_phi_moi))
                else:
                    hang_doi.append((trang_thai_moi, chi_phi_moi))
    return None


# ============================================================
# 3. HIỂN THỊ KẾT QUẢ
# ============================================================


def dinh_dang_hanh_trinh(graph: TransitGraph, hanh_trinh: Journey | None) -> str:
    if hanh_trinh is None:
        return "Không tìm thấy hành trình giữa hai trạm đã chọn."

    def day_du(ma_tram: str) -> str:
        return f"{ma_tram} - {graph.stops[ma_tram]}"

    dong = [
        "KẾT QUẢ TÌM HÀNH TRÌNH",
        "=" * 64,
        f"Trạm đi:  {day_du(hanh_trinh.bat_dau)}",
        f"Trạm đến: {day_du(hanh_trinh.ket_thuc)}",
        "",
    ]
    if not hanh_trinh.segments:
        dong.append("Hai trạm trùng nhau, không cần di chuyển.")
        dong.append("Số đoạn trạm: 0 | Số lần chuyển tuyến: 0")
        return "\n".join(dong)

    cac_doan = hanh_trinh.segments
    i = 0
    buoc = 1
    while i < len(cac_doan):
        ma_tuyen = cac_doan[i].ma_tuyen
        cac_tram = [cac_doan[i].tu_tram]
        while i < len(cac_doan) and cac_doan[i].ma_tuyen == ma_tuyen:
            cac_tram.append(cac_doan[i].den_tram)
            i += 1
        dong.append(f"Bước {buoc}: Đi tuyến {ma_tuyen}")
        dong.append("    " + " → ".join(cac_tram))
        if i < len(cac_doan):
            dong.append(f"    Chuyển tuyến tại {day_du(cac_tram[-1])}")
        dong.append("")
        buoc += 1

    dong.append("-" * 64)
    dong.append(f"Tổng số đoạn trạm: {hanh_trinh.so_doan}")
    dong.append(f"Số lần chuyển tuyến: {hanh_trinh.so_lan_chuyen_tuyen}")
    return "\n".join(dong)


def dinh_dang_danh_sach_tram(graph: TransitGraph) -> str:
    dong = [f"DANH SÁCH {len(graph.stops)} TRẠM XE BUÝT", "=" * 64, ""]
    dong.extend(f"{ma:<6} {ten}" for ma, ten in sorted(graph.stops.items()))
    return "\n".join(dong)


def dinh_dang_danh_sach_tuyen(graph: TransitGraph) -> str:
    dong = [f"DANH SÁCH {len(graph.routes)} TUYẾN XE BUÝT", "=" * 64, ""]
    for ma, cac_tram in sorted(graph.routes.items()):
        dong.append(f"Tuyến {ma} ({len(cac_tram)} trạm)")
        dong.append("    " + " → ".join(cac_tram))
        dong.append("")
    dong.append("Lưu ý: Mỗi tuyến giả lập đi hai chiều giữa các trạm liên tiếp.")
    return "\n".join(dong)


# ============================================================
# 4. THỰC NGHIỆM: 10.000 - 50.000 TRẠM
# ============================================================


def tao_do_thi_lon(so_tram: int) -> TransitGraph:
    """Tạo chuỗi tuyến dài tối đa 50 trạm, hai tuyến liền nhau chung một trạm."""
    if so_tram < 2:
        raise ValueError("Cần ít nhất 2 trạm để tạo đồ thị thử nghiệm.")
    graph = TransitGraph()
    for i in range(1, so_tram + 1):
        graph.add_stop(f"S{i:05d}", f"Trạm giả lập {i}")

    bat_dau = 1
    ma_tuyen = 1
    while bat_dau < so_tram:
        ket_thuc = min(bat_dau + 49, so_tram)
        graph.add_route(f"B{ma_tuyen:04d}", [f"S{i:05d}" for i in range(bat_dau, ket_thuc + 1)])
        bat_dau = ket_thuc
        ma_tuyen += 1
    return graph


def do_thoi_gian_va_bo_nho(ham_tim, graph: TransitGraph, diem_dich: str, so_lan=3):
    cac_lan_ms = []
    bo_nho_peak = []
    for _ in range(so_lan):
        gc.collect()
        tracemalloc.reset_peak()
        truoc, _ = tracemalloc.get_traced_memory()
        moc = perf_counter()
        ket_qua = ham_tim(graph, "S00001", diem_dich)
        cac_lan_ms.append((perf_counter() - moc) * 1000)
        _, dinh = tracemalloc.get_traced_memory()
        bo_nho_peak.append(max(0, dinh - truoc) / 1024**2)
        if ket_qua is None or ket_qua.so_doan != len(graph.stops) - 1:
            raise AssertionError("Đường đi trong phép thử không chính xác.")
        del ket_qua
    return mean(cac_lan_ms), max(bo_nho_peak)


def do_mot_kich_thuoc(so_tram: int, so_lan=3) -> dict:
    gc.collect()
    tracemalloc.start()
    try:
        truoc, _ = tracemalloc.get_traced_memory()
        graph = tao_do_thi_lon(so_tram)
        gc.collect()
        sau, _ = tracemalloc.get_traced_memory()
        graph_mib = max(0, sau - truoc) / 1024**2
        dich = f"S{so_tram:05d}"
        bfs_ms, bfs_mib = do_thoi_gian_va_bo_nho(
            find_shortest_by_stops, graph, dich, so_lan
        )
        doi_ms, doi_mib = do_thoi_gian_va_bo_nho(
            find_fewest_transfers, graph, dich, so_lan
        )
        return {
            "so_tram": so_tram,
            "so_tuyen": len(graph.routes),
            "bo_nho_do_thi_mib": round(graph_mib, 3),
            "bfs_tb_ms": round(bfs_ms, 3),
            "bfs_bo_nho_them_mib": round(bfs_mib, 3),
            "zero_one_bfs_tb_ms": round(doi_ms, 3),
            "zero_one_bfs_bo_nho_them_mib": round(doi_mib, 3),
        }
    finally:
        tracemalloc.stop()


def chay_benchmark(kich_thuoc=(10_000, 30_000, 50_000), so_lan=3, callback=None):
    """Chạy benchmark, tạo CSV cùng thư mục main.py; callback hỗ trợ cập nhật giao diện."""
    ket_qua = []
    for so_tram in kich_thuoc:
        if callback is not None:
            callback(f"Đang đo với {so_tram:,} trạm (mỗi thuật toán {so_lan} lượt)...")
        ket_qua.append(do_mot_kich_thuoc(so_tram, so_lan))
    duong_dan = Path(__file__).resolve().parent / "ket_qua_hieu_nang.csv"
    with open(duong_dan, "w", newline="", encoding="utf-8-sig") as tep:
        writer = csv.DictWriter(tep, fieldnames=list(ket_qua[0]))
        writer.writeheader()
        writer.writerows(ket_qua)
    return ket_qua, duong_dan


def dinh_dang_benchmark(cac_hang: list[dict], duong_dan: Path) -> str:
    dong = [
        "KẾT QUẢ THỰC NGHIỆM HIỆU NĂNG",
        "=" * 64,
        "Mỗi thuật toán chạy 3 lần trên từng đồ thị giả lập.",
        "Các số liệu được đo trên máy đang chạy ứng dụng.",
        "",
    ]
    for h in cac_hang:
        dong.extend([
            f"• {h['so_tram']:,} trạm / {h['so_tuyen']} tuyến",
            f"    Bộ nhớ đồ thị:    {h['bo_nho_do_thi_mib']:.3f} MiB",
            f"    BFS trung bình:   {h['bfs_tb_ms']:.3f} ms",
            f"    0-1 BFS trung bình: {h['zero_one_bfs_tb_ms']:.3f} ms",
            f"    Bộ nhớ thêm BFS / 0-1 BFS: "
            f"{h['bfs_bo_nho_them_mib']:.3f} / {h['zero_one_bfs_bo_nho_them_mib']:.3f} MiB",
            "",
        ])
    dong.extend([
        "Lưu ý: tracemalloc đo các cấp phát Python, không phải tổng RAM tiến trình.",
        f"Đã xuất dữ liệu CSV: {duong_dan}",
    ])
    return "\n".join(dong)


# ============================================================
# 5. KIỂM THỬ TỰ ĐỘNG (16 TRƯỜNG HỢP)
# ============================================================


def hanh_trinh_hop_le(graph: TransitGraph, journey: Journey | None) -> bool:
    if journey is None:
        return False
    hien_tai = journey.bat_dau
    for doan in journey.segments:
        if doan.tu_tram != hien_tai:
            return False
        if (doan.den_tram, doan.ma_tuyen) not in graph.neighbors(hien_tai):
            return False
        hien_tai = doan.den_tram
    return hien_tai == journey.ket_thuc


def so_doan_toi_uu_tham_chieu(graph, start, target):
    q = deque([(start, 0)])
    visited = {start}
    while q:
        stop, count = q.popleft()
        if stop == target:
            return count
        for next_stop, _ in graph.neighbors(stop):
            if next_stop not in visited:
                visited.add(next_stop)
                q.append((next_stop, count + 1))
    return None


def so_chuyen_tuyen_toi_uu_tham_chieu(graph, start, target):
    """Dijkstra độc lập dùng để đối chiếu thuật toán 0-1 BFS."""
    source = (start, "")
    best = {source: 0}
    heap = [(0, source)]
    while heap:
        cost, (stop, route) = heapq.heappop(heap)
        if cost != best[(stop, route)]:
            continue
        if stop == target:
            return cost
        for neighbor, new_route in graph.neighbors(stop):
            extra = int(bool(route) and route != new_route)
            candidate = cost + extra
            state = (neighbor, new_route)
            if candidate < best.get(state, float("inf")):
                best[state] = candidate
                heapq.heappush(heap, (candidate, state))
    return None


class KiemThuDe17(unittest.TestCase):
    def setUp(self):
        self.graph = create_demo_graph()

    def test_du_lieu_25_tram_8_tuyen(self):
        self.assertEqual(len(self.graph.stops), 25)
        self.assertEqual(len(self.graph.routes), 8)

    def test_cung_tuyen(self):
        journey = find_shortest_by_stops(self.graph, "S01", "S06")
        self.assertTrue(hanh_trinh_hop_le(self.graph, journey))
        self.assertEqual((journey.so_doan, journey.so_lan_chuyen_tuyen), (5, 0))

    def test_tim_duong_mau(self):
        bfs = find_shortest_by_stops(self.graph, "S01", "S14")
        transfer = find_fewest_transfers(self.graph, "S01", "S14")
        self.assertTrue(hanh_trinh_hop_le(self.graph, bfs))
        self.assertTrue(hanh_trinh_hop_le(self.graph, transfer))
        self.assertEqual(bfs.so_doan, 8)
        self.assertEqual(transfer.so_lan_chuyen_tuyen, 2)

    def test_phan_biet_hai_tieu_chi(self):
        graph = TransitGraph()
        for s in ("A", "B", "X", "Y", "E"):
            graph.add_stop(s, s)
        graph.add_route("R1", ["A", "X", "Y", "E"])
        graph.add_route("R2", ["A", "B"])
        graph.add_route("R3", ["B", "E"])
        bfs = find_shortest_by_stops(graph, "A", "E")
        transfer = find_fewest_transfers(graph, "A", "E")
        self.assertEqual((bfs.so_doan, bfs.so_lan_chuyen_tuyen), (2, 1))
        self.assertEqual((transfer.so_doan, transfer.so_lan_chuyen_tuyen), (3, 0))

    def test_trung_tram(self):
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            journey = ham(self.graph, "S04", "S04")
            self.assertEqual((journey.so_doan, journey.so_lan_chuyen_tuyen), (0, 0))

    def test_khong_co_duong(self):
        graph = TransitGraph()
        for s in ("A", "B", "C"):
            graph.add_stop(s, s)
        graph.add_route("R1", ["A", "B"])
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            self.assertIsNone(ham(graph, "A", "C"))

    def test_tram_sai(self):
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            with self.assertRaises(ValueError):
                ham(self.graph, "S01", "S99")

    def test_chuan_hoa_ma(self):
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            journey = ham(self.graph, " s01 ", " s02 ")
            self.assertEqual(journey.so_doan, 1)

    def test_tuyen_chua_tram_khong_ton_tai(self):
        graph = TransitGraph()
        graph.add_stop("A", "A")
        graph.add_stop("B", "B")
        with self.assertRaises(ValueError):
            graph.add_route("R1", ["A", "X"])
        self.assertEqual(graph.routes, {})
        self.assertEqual(graph.neighbors("A"), [])

    def test_tuyen_lap_tram(self):
        with self.assertRaises(ValueError):
            self.graph.add_route("R9", ["S01", "S02", "S01"])

    def test_tuyen_lap_ma(self):
        with self.assertRaises(ValueError):
            self.graph.add_route("T01", ["S01", "S02"])

    def test_du_lieu_lon_nho(self):
        graph = tao_do_thi_lon(100)
        self.assertEqual(len(graph.stops), 100)
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            j = ham(graph, "S00001", "S00100")
            self.assertEqual(j.so_doan, 99)
            self.assertTrue(hanh_trinh_hop_le(graph, j))

    def test_tuyen_hai_chieu(self):
        # Các tuyến mẫu cho phép đi cả chiều xuôi và ngược.
        for ham in (find_shortest_by_stops, find_fewest_transfers):
            journey = ham(self.graph, "S06", "S01")
            self.assertTrue(hanh_trinh_hop_le(self.graph, journey))
            self.assertEqual((journey.so_doan, journey.so_lan_chuyen_tuyen), (5, 0))

    def test_tuyen_thieu_tram(self):
        graph = TransitGraph()
        graph.add_stop("A", "Trạm A")
        with self.assertRaises(ValueError):
            graph.add_route("R1", ["A"])
        self.assertEqual(graph.routes, {})

    def test_tram_trung_ma(self):
        with self.assertRaises(ValueError):
            self.graph.add_stop(" s01 ", "Trạm bị lặp")
        self.assertEqual(len(self.graph.stops), 25)

    def test_ngau_nhien_so_sanh_dijkstra(self):
        rng = random.Random(2026)
        for _ in range(80):
            graph = TransitGraph()
            count = rng.randint(3, 9)
            nodes = [f"N{i}" for i in range(count)]
            for node in nodes:
                graph.add_stop(node, node)
            for rid in range(rng.randint(1, 7)):
                route_nodes = rng.sample(nodes, rng.randint(2, min(count, 6)))
                graph.add_route(f"R{rid}", route_nodes)
            for _ in range(5):
                start, end = rng.sample(nodes, 2)
                expected_stops = so_doan_toi_uu_tham_chieu(graph, start, end)
                expected_transfers = so_chuyen_tuyen_toi_uu_tham_chieu(graph, start, end)
                bfs = find_shortest_by_stops(graph, start, end)
                transfer = find_fewest_transfers(graph, start, end)
                if expected_stops is None:
                    self.assertIsNone(bfs)
                else:
                    self.assertTrue(hanh_trinh_hop_le(graph, bfs))
                    self.assertEqual(bfs.so_doan, expected_stops)
                if expected_transfers is None:
                    self.assertIsNone(transfer)
                else:
                    self.assertTrue(hanh_trinh_hop_le(graph, transfer))
                    self.assertEqual(transfer.so_lan_chuyen_tuyen, expected_transfers)


def chay_kiem_thu() -> tuple[bool, str]:
    stream = io.StringIO()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(KiemThuDe17)
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    return result.wasSuccessful(), stream.getvalue()


# ============================================================
# 6. GIAO DIỆN TKINTER: MỘT FILE, KHÔNG DÙNG THƯ VIỆN NGOÀI
# ============================================================


def mo_giao_dien() -> None:
    try:
        import tkinter as tk
        from tkinter import messagebox, scrolledtext, ttk
    except ImportError as exc:
        raise SystemExit(
            "Máy chưa có Tkinter. Trên Ubuntu có thể cài gói python3-tk."
        ) from exc

    # Dùng màu xanh - vàng thống nhất với mẫu slide báo cáo của nhóm.
    XANH = "#123F8B"
    XANH_DAM = "#0D2D63"
    VANG = "#E9AD20"
    NEN = "#F2F5FA"
    TRANG = "#FFFFFF"
    CHU = "#1E304A"
    PHU = "#637187"

    class BusApp:
        def __init__(self, root):
            self.root = root
            self.graph = create_demo_graph()
            self.events = Queue()
            self.dang_do = False
            self.root.title("Đề tài 17 | Mô phỏng lịch trình xe buýt")
            self.root.geometry("1160x790")
            self.root.minsize(940, 670)
            self.root.configure(bg=NEN)
            self.status = tk.StringVar(value="Sẵn sàng: chọn hai trạm và thuật toán tìm hành trình.")

            style = ttk.Style(root)
            if "clam" in style.theme_names():
                style.theme_use("clam")
            style.configure("App.TFrame", background=NEN)
            style.configure("Card.TFrame", background=TRANG)
            style.configure("Card.TLabel", background=TRANG, foreground=CHU, font=("Segoe UI", 10))
            style.configure("Muted.TLabel", background=TRANG, foreground=PHU, font=("Segoe UI", 9))
            style.configure("Section.TLabel", background=TRANG, foreground=CHU, font=("Segoe UI", 12, "bold"))
            style.configure("AppMuted.TLabel", background=NEN, foreground=PHU, font=("Segoe UI", 9))
            style.configure("Main.TButton", padding=(11, 10), font=("Segoe UI", 10, "bold"),
                            background=XANH, foreground=TRANG)
            style.map("Main.TButton", background=[("active", XANH_DAM), ("disabled", "#CBD5E2")],
                      foreground=[("disabled", "#6D7B90")])
            style.configure("Alt.TButton", padding=(9, 9), font=("Segoe UI", 9),
                            background="#E8EFFA", foreground=XANH_DAM)
            style.map("Alt.TButton", background=[("active", "#D6E3F8")])
            style.configure("Entry.TCombobox", padding=7, font=("Segoe UI", 10))
            style.configure("Custom.Treeview", rowheight=30, font=("Segoe UI", 10),
                            background=TRANG, foreground=CHU, fieldbackground=TRANG)
            style.configure("Custom.Treeview.Heading", font=("Segoe UI", 10, "bold"),
                            background="#E8EFFA", foreground=XANH_DAM)
            style.map("Custom.Treeview", background=[("selected", "#D6E8FF")],
                      foreground=[("selected", XANH_DAM)])
            style.configure("App.TNotebook", background=NEN, borderwidth=0)
            style.configure("App.TNotebook.Tab", padding=(18, 10), font=("Segoe UI", 10, "bold"))
            style.map("App.TNotebook.Tab", background=[("selected", TRANG), ("!selected", "#E2EAF5")],
                      foreground=[("selected", XANH), ("!selected", PHU)])

            # Header cố định: bố cục tương đồng với slide báo cáo của trường.
            hero = tk.Frame(root, bg=XANH_DAM, padx=25, pady=17)
            hero.pack(fill="x")
            tk.Frame(hero, bg=VANG, height=4).pack(fill="x", side="bottom", pady=(14, 0))
            tk.Button(hero, text="Thoát", command=root.destroy, bg="#244D8C", fg=TRANG,
                      activebackground="#325E9E", activeforeground=TRANG,
                      relief="flat", padx=13, pady=5,
                      font=("Segoe UI", 9, "bold")).place(relx=0.99, y=1, anchor="ne")
            tk.Label(hero, text="ĐỀ TÀI 17  /  CẤU TRÚC DỮ LIỆU & GIẢI THUẬT",
                     bg=XANH_DAM, fg="#F6CA69", font=("Segoe UI", 10, "bold"),
                     anchor="w").pack(fill="x")
            tk.Label(hero, text="MÔ PHỎNG LỊCH TRÌNH XE BUÝT",
                     bg=XANH_DAM, fg=TRANG, font=("Segoe UI", 20, "bold"),
                     anchor="w").pack(fill="x", pady=(4, 2))
            tk.Label(hero, text="PYTHON + TKINTER     •     25 trạm     •     8 tuyến     •     Graph / BFS / 0-1 BFS",
                     bg=XANH_DAM, fg="#D9E6FA", font=("Segoe UI", 10),
                     anchor="w").pack(fill="x")

            body = ttk.Frame(root, style="App.TFrame", padding=(20, 14, 20, 8))
            body.pack(fill="both", expand=True)
            self.tabs = ttk.Notebook(body, style="App.TNotebook")
            self.tabs.pack(fill="both", expand=True)
            self.tab_tim = ttk.Frame(self.tabs, style="App.TFrame")
            self.tab_du_lieu = ttk.Frame(self.tabs, style="App.TFrame")
            self.tab_danh_gia = ttk.Frame(self.tabs, style="App.TFrame")
            self.tabs.add(self.tab_tim, text="01   TÌM HÀNH TRÌNH")
            self.tabs.add(self.tab_du_lieu, text="02   TRẠM & TUYẾN XE")
            self.tabs.add(self.tab_danh_gia, text="03   KIỂM THỬ & HIỆU NĂNG")

            self._tao_tab_tim(tk, ttk, scrolledtext)
            self._tao_tab_du_lieu(tk, ttk, scrolledtext)
            self._tao_tab_danh_gia(tk, ttk, scrolledtext)

            footer = tk.Frame(root, bg="#E6EDF8", padx=20, pady=9)
            footer.pack(fill="x")
            tk.Label(footer, textvariable=self.status, bg="#E6EDF8", fg=XANH_DAM,
                     font=("Segoe UI", 9), anchor="w").pack(fill="x")

            self._xem_danh_sach_tram()
            self._xem_danh_sach_tuyen()
            self.tim_duong(False)
            self.root.after(150, self.xu_ly_su_kien)

        def _tao_tab_tim(self, tk, ttk, scrolledtext):
            self.tab_tim.columnconfigure(0, weight=1, minsize=295)
            self.tab_tim.columnconfigure(1, weight=3)
            self.tab_tim.rowconfigure(0, weight=1)

            left = ttk.Frame(self.tab_tim, style="Card.TFrame", padding=18)
            left.grid(row=0, column=0, sticky="nsew", pady=(12, 0), padx=(0, 11))
            right = ttk.Frame(self.tab_tim, style="Card.TFrame", padding=16)
            right.grid(row=0, column=1, sticky="nsew", pady=(12, 0))
            right.columnconfigure(0, weight=1)
            right.rowconfigure(4, weight=1)
            right.rowconfigure(6, weight=1)

            ttk.Label(left, text="THÔNG TIN CHUYẾN ĐI", style="Section.TLabel").pack(anchor="w", pady=(0, 15))
            ttk.Label(left, text="Trạm xuất phát", style="Card.TLabel").pack(anchor="w")
            stations = [f"{ma} | {ten}" for ma, ten in sorted(self.graph.stops.items())]
            self.tram_di = ttk.Combobox(left, values=stations, state="readonly", style="Entry.TCombobox")
            self.tram_di.pack(fill="x", pady=(6, 11))
            self.tram_di.current(0)
            ttk.Label(left, text="Trạm đích", style="Card.TLabel").pack(anchor="w")
            self.tram_den = ttk.Combobox(left, values=stations, state="readonly", style="Entry.TCombobox")
            self.tram_den.pack(fill="x", pady=(6, 10))
            self.tram_den.current(13)
            ttk.Button(left, text="⇅  Đảo chiều hành trình", style="Alt.TButton",
                       command=self.dao_chieu).pack(fill="x", pady=(0, 19))

            ttk.Label(left, text="CHỌN CÁCH TÌM", style="Section.TLabel").pack(anchor="w", pady=(0, 10))
            ttk.Button(left, text="BFS  ·  Ít đoạn trạm", style="Main.TButton",
                       command=lambda: self.tim_duong(False)).pack(fill="x", pady=(0, 9))
            ttk.Button(left, text="0-1 BFS  ·  Ít chuyển tuyến", style="Main.TButton",
                       command=lambda: self.tim_duong(True)).pack(fill="x", pady=(0, 16))
            ttk.Label(left, text="BFS ưu tiên số đoạn đi qua.\n0-1 BFS ưu tiên số lần đổi xe.\nChưa tính thời gian hoặc giá vé.",
                      style="Muted.TLabel", justify="left", wraplength=280).pack(anchor="w")
            ttk.Separator(left).pack(fill="x", pady=(18, 14))
            ttk.Button(left, text="Xem danh sách trạm / tuyến", style="Alt.TButton",
                       command=lambda: self.tabs.select(self.tab_du_lieu)).pack(fill="x")

            ttk.Label(right, text="KẾT QUẢ HÀNH TRÌNH", style="Section.TLabel").grid(row=0, column=0, sticky="w")
            self.ten_thuat_toan = ttk.Label(right, text="BFS · Ít đoạn trạm", style="Muted.TLabel")
            self.ten_thuat_toan.grid(row=1, column=0, sticky="w", pady=(2, 12))
            metrics = ttk.Frame(right, style="Card.TFrame")
            metrics.grid(row=2, column=0, sticky="ew", pady=(0, 14))
            for c in range(3):
                metrics.columnconfigure(c, weight=1)
            self.metric_doan = self._metric(metrics, 0, "SỐ ĐOẠN")
            self.metric_doi = self._metric(metrics, 1, "LẦN CHUYỂN TUYẾN")
            self.metric_tuyen = self._metric(metrics, 2, "TUYẾN ĐÃ DÙNG")

            ttk.Label(right, text="Chi tiết từng đoạn", style="Card.TLabel").grid(row=3, column=0, sticky="w", pady=(0, 7))
            rows = ttk.Frame(right, style="Card.TFrame")
            rows.grid(row=4, column=0, sticky="nsew")
            rows.rowconfigure(0, weight=1)
            rows.columnconfigure(0, weight=1)
            self.bang_hanh_trinh = ttk.Treeview(rows, columns=("stt", "tuyen", "tu", "den"),
                                               show="headings", height=8, style="Custom.Treeview")
            for col, title, width, stretch in [
                ("stt", "Bước", 55, False), ("tuyen", "Tuyến", 75, False),
                ("tu", "Từ trạm", 105, True), ("den", "Đến trạm", 105, True)
            ]:
                self.bang_hanh_trinh.heading(col, text=title)
                self.bang_hanh_trinh.column(col, width=width, minwidth=50, anchor="center" if col in ("stt", "tuyen") else "w", stretch=stretch)
            scroll = ttk.Scrollbar(rows, command=self.bang_hanh_trinh.yview)
            self.bang_hanh_trinh.configure(yscrollcommand=scroll.set)
            self.bang_hanh_trinh.grid(row=0, column=0, sticky="nsew")
            scroll.grid(row=0, column=1, sticky="ns")

            ttk.Label(right, text="Hướng dẫn lên xe / điểm đổi tuyến", style="Card.TLabel").grid(
                row=5, column=0, sticky="w", pady=(11, 6))
            self.huong_dan = scrolledtext.ScrolledText(right, height=6, wrap="word", font=("Segoe UI", 10),
                                                      bg="#F6F8FC", fg=CHU, padx=12, pady=9,
                                                      relief="flat", state="disabled")
            self.huong_dan.grid(row=6, column=0, sticky="nsew")

        def _metric(self, parent, column, heading):
            frame = ttk.Frame(parent, style="Card.TFrame")
            frame.grid(row=0, column=column, sticky="ew", padx=(0, 10) if column < 2 else 0)
            ttk.Label(frame, text=heading, style="Muted.TLabel").pack(anchor="w")
            var = tk.StringVar(value="—")
            label = tk.Label(frame, textvariable=var, bg="#FFFFFF", fg="#123F8B",
                                                 font=("Segoe UI", 18, "bold"), anchor="w")
            label.pack(fill="x", pady=(1, 0))
            return var

        def _tao_tab_du_lieu(self, tk, ttk, scrolledtext):
            page = ttk.Frame(self.tab_du_lieu, style="Card.TFrame", padding=18)
            page.pack(fill="both", expand=True, pady=(12, 0))
            ttk.Label(page, text="DỮ LIỆU MẠNG LƯỚI XE BUÝT", style="Section.TLabel").pack(anchor="w")
            ttk.Label(page, text="Bộ dữ liệu giả lập gồm 25 trạm, 8 tuyến; các tuyến đi hai chiều.",
                      style="Muted.TLabel").pack(anchor="w", pady=(4, 14))
            panes = ttk.Panedwindow(page, orient="horizontal")
            panes.pack(fill="both", expand=True)
            frm1 = ttk.Frame(panes, style="Card.TFrame")
            frm2 = ttk.Frame(panes, style="Card.TFrame")
            panes.add(frm1, weight=1)
            panes.add(frm2, weight=1)
            frm1.rowconfigure(1, weight=1)
            frm1.columnconfigure(0, weight=1)
            frm2.rowconfigure(1, weight=1)
            frm2.columnconfigure(0, weight=1)
            ttk.Label(frm1, text="DANH SÁCH TRẠM", style="Section.TLabel").grid(row=0, column=0, sticky="w", pady=(0, 8))
            self.bang_tram = ttk.Treeview(frm1, columns=("ma", "ten"), show="headings", style="Custom.Treeview")
            self.bang_tram.heading("ma", text="Mã trạm")
            self.bang_tram.heading("ten", text="Tên trạm")
            self.bang_tram.column("ma", width=100, anchor="center", stretch=False)
            self.bang_tram.column("ten", width=240)
            self.bang_tram.grid(row=1, column=0, sticky="nsew", padx=(0, 15))
            ttk.Label(frm2, text="DANH SÁCH TUYẾN", style="Section.TLabel").grid(row=0, column=0, sticky="w", pady=(0, 8))
            self.bang_tuyen = ttk.Treeview(frm2, columns=("ma", "so", "dau", "cuoi"),
                                          show="headings", height=10, style="Custom.Treeview")
            for col, title, wd in [("ma", "Tuyến", 78), ("so", "Trạm", 64), ("dau", "Bắt đầu", 90), ("cuoi", "Kết thúc", 90)]:
                self.bang_tuyen.heading(col, text=title)
                self.bang_tuyen.column(col, width=wd, anchor="center")
            self.bang_tuyen.grid(row=1, column=0, sticky="nsew")
            self.bang_tuyen.bind("<<TreeviewSelect>>", self._chon_tuyen)
            ttk.Label(frm2, text="Thứ tự trạm trên tuyến đang chọn", style="Card.TLabel").grid(
                row=2, column=0, sticky="w", pady=(12, 6))
            self.tuyen_chi_tiet = scrolledtext.ScrolledText(frm2, height=5, wrap="word",
                                                            font=("Segoe UI", 10), bg="#F6F8FC",
                                                            fg=CHU, relief="flat", state="disabled")
            self.tuyen_chi_tiet.grid(row=3, column=0, sticky="ew", pady=(0, 4))

        def _tao_tab_danh_gia(self, tk, ttk, scrolledtext):
            page = ttk.Frame(self.tab_danh_gia, style="Card.TFrame", padding=18)
            page.pack(fill="both", expand=True, pady=(12, 0))
            ttk.Label(page, text="KIỂM THỬ VÀ ĐÁNH GIÁ HIỆU NĂNG", style="Section.TLabel").pack(anchor="w")
            ttk.Label(page, text="Bài kiểm thử tự động và thực nghiệm trên đồ thị giả lập 10.000 / 30.000 / 50.000 trạm.",
                      style="Muted.TLabel").pack(anchor="w", pady=(3, 15))
            controls = ttk.Frame(page, style="Card.TFrame")
            controls.pack(fill="x", pady=(0, 12))
            ttk.Button(controls, text="Chạy kiểm thử", style="Main.TButton",
                       command=self.kiem_thu).pack(side="left", padx=(0, 10))
            self.benchmark_button = ttk.Button(controls, text="Đo hiệu năng + xuất CSV", style="Alt.TButton",
                                               command=self.bat_dau_benchmark)
            self.benchmark_button.pack(side="left")
            ttk.Label(page, text="Nhật ký kết quả", style="Card.TLabel").pack(anchor="w", pady=(0, 6))
            self.log = scrolledtext.ScrolledText(page, wrap="word", font=("Consolas", 10),
                                                  bg="#F6F8FC", fg=CHU, padx=12, pady=12,
                                                  relief="flat", state="disabled")
            self.log.pack(fill="both", expand=True)
            self._viet_text(self.log, "Chọn 'Chạy kiểm thử' để kiểm tra chương trình.\n\n"
                            "Chọn 'Đo hiệu năng + xuất CSV' để thực nghiệm với dữ liệu lớn.\n"
                            "Phép đo chạy ở luồng riêng để cửa sổ vẫn phản hồi.\n\n"
                            "Lưu ý: kết quả thời gian thay đổi tùy cấu hình máy.")

        @staticmethod
        def _viet_text(widget, content):
            widget.configure(state="normal")
            widget.delete("1.0", "end")
            widget.insert("1.0", content)
            widget.configure(state="disabled")
            widget.yview_moveto(0)

        def _xem_danh_sach_tram(self):
            for ma, ten in sorted(self.graph.stops.items()):
                self.bang_tram.insert("", "end", values=(ma, ten))

        def _xem_danh_sach_tuyen(self):
            for ma, cac_tram in sorted(self.graph.routes.items()):
                self.bang_tuyen.insert("", "end", iid=ma,
                                      values=(ma, len(cac_tram), cac_tram[0], cac_tram[-1]))
            self.bang_tuyen.selection_set("T01")
            self._chon_tuyen()

        def _chon_tuyen(self, event=None):
            selected = self.bang_tuyen.selection()
            if not selected:
                return
            ma = selected[0]
            danh_sach = self.graph.routes[ma]
            lines = [f"Tuyến {ma} · {len(danh_sach)} trạm · hoạt động hai chiều", ""]
            lines.extend(f"{i:02d}. {tram} - {self.graph.stops[tram]}" for i, tram in enumerate(danh_sach, 1))
            self._viet_text(self.tuyen_chi_tiet, "\n".join(lines))

        def lay_ma_tram(self, combo):
            gia_tri = combo.get()
            if not gia_tri:
                raise ValueError("Vui lòng chọn trạm xuất phát và trạm đích.")
            return gia_tri.split(" | ", 1)[0]

        def dao_chieu(self):
            a, b = self.tram_di.current(), self.tram_den.current()
            self.tram_di.current(b)
            self.tram_den.current(a)
            self.tim_duong(False)

        def tim_duong(self, it_chuyen_tuyen):
            try:
                start = self.lay_ma_tram(self.tram_di)
                target = self.lay_ma_tram(self.tram_den)
                func = find_fewest_transfers if it_chuyen_tuyen else find_shortest_by_stops
                journey = func(self.graph, start, target)
            except ValueError as exc:
                messagebox.showerror("Dữ liệu chưa hợp lệ", str(exc))
                return

            self.ten_thuat_toan.configure(text=("0-1 BFS · Ít chuyển tuyến" if it_chuyen_tuyen
                                               else "BFS · Ít đoạn trạm"))
            for row in self.bang_hanh_trinh.get_children():
                self.bang_hanh_trinh.delete(row)
            if journey is None:
                self.metric_doan.set("—")
                self.metric_doi.set("—")
                self.metric_tuyen.set("—")
                self._viet_text(self.huong_dan, "Không tìm thấy hành trình nối hai trạm đã chọn.")
                self.status.set("Không tìm thấy đường đi giữa hai trạm.")
                return

            used_lines = list(dict.fromkeys(s.ma_tuyen for s in journey.segments))
            self.metric_doan.set(str(journey.so_doan))
            self.metric_doi.set(str(journey.so_lan_chuyen_tuyen))
            self.metric_tuyen.set(str(len(used_lines)))
            for i, s in enumerate(journey.segments, start=1):
                self.bang_hanh_trinh.insert("", "end", values=(i, s.ma_tuyen, s.tu_tram, s.den_tram))
            self._viet_text(self.huong_dan, dinh_dang_hanh_trinh(self.graph, journey))
            self.status.set(f"{start} → {target}: {journey.so_doan} đoạn, "
                            f"{journey.so_lan_chuyen_tuyen} lần chuyển tuyến.")

        def kiem_thu(self):
            if self.dang_do:
                messagebox.showinfo("Đang thực nghiệm", "Vui lòng đợi phép đo hiệu năng hoàn thành.")
                return
            ok, details = chay_kiem_thu()
            self._viet_text(self.log, "KẾT QUẢ KIỂM THỬ TỰ ĐỘNG\n" + "=" * 60 + "\n\n" + details)
            self.status.set("Kiểm thử đã hoàn thành: ĐẠT." if ok else "Kiểm thử: CÓ TRƯỜNG HỢP KHÔNG ĐẠT.")

        def bat_dau_benchmark(self):
            if self.dang_do:
                return
            self.dang_do = True
            self.benchmark_button.configure(state="disabled")
            self._viet_text(self.log,
                            "ĐANG ĐO HIỆU NĂNG\n" + "=" * 60 + "\n\n"
                            "Dữ liệu: 10.000 / 30.000 / 50.000 trạm.\n"
                            "Hai thuật toán được chạy 3 lượt mỗi kích thước.\n"
                            "Dữ liệu CSV được lưu tại thư mục chứa main.py.\n\n"
                            "Vui lòng theo dõi trạng thái bên dưới.")
            self.status.set("Đang thực nghiệm ở luồng riêng... cửa sổ vẫn sử dụng được.")

            def worker():
                try:
                    rows, path = chay_benchmark(callback=lambda msg: self.events.put(("progress", msg)))
                    self.events.put(("done", (rows, path)))
                except Exception as exc:
                    self.events.put(("error", str(exc)))

            threading.Thread(target=worker, daemon=True).start()

        def xu_ly_su_kien(self):
            try:
                while True:
                    event, payload = self.events.get_nowait()
                    if event == "progress":
                        self.status.set(payload)
                    elif event == "done":
                        rows, path = payload
                        self._viet_text(self.log, dinh_dang_benchmark(rows, path))
                        self.status.set("Đã đo hiệu năng và lưu file CSV.")
                        self.dang_do = False
                        self.benchmark_button.configure(state="normal")
                    elif event == "error":
                        self._viet_text(self.log, "ĐO HIỆU NĂNG BỊ LỖI:\n" + payload)
                        self.status.set("Đo hiệu năng chưa thành công.")
                        self.dang_do = False
                        self.benchmark_button.configure(state="normal")
                        messagebox.showerror("Đo hiệu năng", payload)
            except Empty:
                pass
            # after chỉ chạy trên luồng giao diện; luồng đo không đụng trực tiếp Tkinter.
            self.root.after(150, self.xu_ly_su_kien)

    try:
        root = tk.Tk()
    except tk.TclError as exc:
        raise SystemExit("Không mở được cửa sổ Tkinter (cần máy có màn hình đồ họa). " + str(exc)) from exc
    BusApp(root)
    root.mainloop()


# ============================================================
# 7. ĐIỂM CHẠY DUY NHẤT
# ============================================================


def main() -> int:
    if "--test" in sys.argv:
        ok, info = chay_kiem_thu()
        print(info)
        return 0 if ok else 1
    if "--benchmark" in sys.argv:
        print("Đang đo 10.000, 30.000 và 50.000 trạm...")
        rows, filepath = chay_benchmark(callback=print)
        print(dinh_dang_benchmark(rows, filepath))
        return 0
    mo_giao_dien()
    return 0


if __name__ == "__main__":
    sys.exit(main())
