-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:05.364079+00:00
-- url     : https://prove2.me/theorems/ce9f6242-56a0-4c10-94b5-7a9007787131
-- title:
--   Edge bound for connected drawn planar graphs
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
