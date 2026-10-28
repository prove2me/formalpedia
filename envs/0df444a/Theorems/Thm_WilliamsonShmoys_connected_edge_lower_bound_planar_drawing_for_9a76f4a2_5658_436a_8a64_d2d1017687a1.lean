-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- name    : WilliamsonShmoys.connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:55:49.005979+00:00
-- url     : https://prove2.me/theorems/52687827-ae9a-4dfb-9238-f5927d0559fe
-- title:
--   Connected finite graph edge lower bound
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices. A spanning tree and the finite-tree edge count provide an independent proof route; this removes the graph-theoretic lower-bound work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hconn : L.Connected) :
    Fintype.card V - 1 <= L.edgeSet.ncard := by sorry
