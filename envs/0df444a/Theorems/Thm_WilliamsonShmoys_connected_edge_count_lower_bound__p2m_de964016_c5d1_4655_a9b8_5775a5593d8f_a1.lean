-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- name    : WilliamsonShmoys.connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:02.798293+00:00
-- url     : https://prove2.me/theorems/5082cc2c-d2ae-4cce-8f02-4e4f192755d4
-- title:
--   Edge lower bound for a finite connected graph
-- statement:
--   A finite connected graph has at least |V|−1 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) : Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
