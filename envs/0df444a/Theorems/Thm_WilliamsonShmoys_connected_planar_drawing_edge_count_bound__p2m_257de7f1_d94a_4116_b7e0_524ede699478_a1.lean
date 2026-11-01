-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count_bound__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:25.065806+00:00
-- url     : https://prove2.me/theorems/344171ca-a6db-4d8b-baba-27cf92701308
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. This isolates the Euler-counting step from the parent’s disconnected case. A proof route is to construct the plane embedding’s face boundary walks, establish Euler’s formula, show each face boundary walk has length at least three, and count each edge twice across face sides. The connected plane-embedding and face-counting argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_count_bound__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
