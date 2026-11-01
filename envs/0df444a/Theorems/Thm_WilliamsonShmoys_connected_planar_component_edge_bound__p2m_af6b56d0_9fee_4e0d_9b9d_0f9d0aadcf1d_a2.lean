-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- name    : WilliamsonShmoys.connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:00.8362+00:00
-- url     : https://prove2.me/theorems/cc516969-790b-410d-8fc5-8fd17bba7f5b
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   For a connected finite simple graph with a crossing-free drawing and at least three vertices, establish the usual planar edge bound. This isolates the topological core: derive Euler’s formula for the drawing, count face-edge incidences, and use simplicity and the vertex lower bound to control face boundaries. The one- and two-vertex cases are deliberately excluded; component aggregation handles them separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card U := by
  sorry
