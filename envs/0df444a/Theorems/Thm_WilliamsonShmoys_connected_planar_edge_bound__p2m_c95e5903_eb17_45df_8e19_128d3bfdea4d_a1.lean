-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:05.91379+00:00
-- url     : https://prove2.me/theorems/55f47020-da90-4034-b4af-759a470f5d81
-- title:
--   Euler edge bound for a connected drawable simple graph
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges. This child removes the Euler counting step from the parent. An independent route is to derive a plane embedding, apply Euler's formula, count two edge incidences per edge, and use simplicity and the vertex lower bound to bound each face boundary below by three. The remaining obligation is to formalize that Euler and face-count argument for the drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
