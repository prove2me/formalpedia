-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:14.863268+00:00
-- url     : https://prove2.me/theorems/7cf11437-ccf4-4d59-ac0e-83c393976ef1
-- title:
--   Connected planar graph edge bound
-- statement:
--   A connected graph with a crossing-free drawing on a finite ordered vertex type and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
