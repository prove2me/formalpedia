-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:30.822193+00:00
-- url     : https://prove2.me/theorems/94535f0f-7fcf-46ec-8860-fc174f378d1a
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   Prove the usual edge bound for a connected finite simple graph with the given crossing-free drawing and at least three vertices. This isolates the Euler-counting argument from the parent’s disconnected-graph handling. A proof route is to convert the drawing to a plane embedding, apply Euler’s formula, and count edge incidences along face boundaries; connectedness, simplicity, and the vertex lower bound are needed for that count. Establishing those results for this exact drawing predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
