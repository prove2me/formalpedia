-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- name    : WilliamsonShmoys.connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:06.701178+00:00
-- url     : https://prove2.me/theorems/2c76ab23-aade-4532-a35e-5e2cbf29bb25
-- title:
--   Euler edge bound for a connected graph with a crossing-free drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing as defined by `HasPlanarDrawingOn` has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
