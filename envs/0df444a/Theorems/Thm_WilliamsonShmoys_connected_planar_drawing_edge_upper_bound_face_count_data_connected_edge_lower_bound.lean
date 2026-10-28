-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:06:37.728439+00:00
-- url     : https://prove2.me/theorems/af22e2e8-54fa-4fb2-a638-6a148928d7b3
-- title:
--   Connected graph edge lower bound for face-count data
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices. This supplies the lower bound needed to justify the chosen natural-number difference in the parent. A proof route is to take a spanning tree of the connected graph, count its edges as `card V - 1`, and use that its edge set is contained in the graph's edge set. The statement has no planar or `card V ≥ 3` hypothesis because neither is needed; the one-vertex boundary case satisfies the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by sorry
