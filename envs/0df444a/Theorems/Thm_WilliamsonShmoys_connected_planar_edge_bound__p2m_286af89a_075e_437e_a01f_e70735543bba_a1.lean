-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:11.485073+00:00
-- url     : https://prove2.me/theorems/688f1835-390c-48d2-a756-3ce127433083
-- title:
--   Edge bound for connected planar simple graphs
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
