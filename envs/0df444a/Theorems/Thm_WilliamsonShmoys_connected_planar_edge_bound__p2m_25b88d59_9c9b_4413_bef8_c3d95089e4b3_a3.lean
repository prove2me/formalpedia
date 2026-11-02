-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:22.304214+00:00
-- url     : https://prove2.me/theorems/69e73f60-1756-4e30-afbd-efe3ac2bd3ed
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
