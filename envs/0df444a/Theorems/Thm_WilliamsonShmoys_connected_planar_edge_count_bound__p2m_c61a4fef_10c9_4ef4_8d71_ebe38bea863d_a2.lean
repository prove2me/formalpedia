-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:31.073517+00:00
-- url     : https://prove2.me/theorems/6b80c57f-d6b2-44cb-abfd-7ee90432d85d
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with at least three vertices and the specified planar drawing has at most 3n−6 edges. The proof route is Euler’s formula for a connected plane graph and the face-boundary incidence count, including the boundary cases needed for connected simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hConnected : L.Connected) (hDraw : HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
