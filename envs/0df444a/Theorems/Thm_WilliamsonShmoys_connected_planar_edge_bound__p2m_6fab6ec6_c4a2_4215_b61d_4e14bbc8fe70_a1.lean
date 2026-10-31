-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:48.372983+00:00
-- url     : https://prove2.me/theorems/b70d6e42-d406-4a6d-93af-72acb122af30
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph on at least three vertices with a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
