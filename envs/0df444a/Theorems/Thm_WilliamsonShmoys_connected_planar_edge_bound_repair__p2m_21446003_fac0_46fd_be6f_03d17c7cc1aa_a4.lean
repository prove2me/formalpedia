-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- name    : WilliamsonShmoys.connected_planar_edge_bound_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:43.976108+00:00
-- url     : https://prove2.me/theorems/b96ca547-b898-4690-ad60-bc0215b36cee
-- title:
--   Edge bound for connected planar graphs
-- statement:
--   Prove the standard edge bound for a finite connected simple graph with a crossing-free drawing and at least three vertices. This isolates the Euler-formula argument and the face-boundary estimates, including exceptional short-face cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
