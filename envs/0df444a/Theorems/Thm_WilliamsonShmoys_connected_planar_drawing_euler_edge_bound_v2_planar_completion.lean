-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_edge_bound_v2_planar_completion
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2_planar_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:38:26.941223+00:00
-- url     : https://prove2.me/theorems/fe2db72e-aabe-4cc0-aa24-14232c0d3d01
-- title:
--   Planar completion with extremal edge count
-- statement:
--   A connected finite graph with at least three vertices and a crossing-free drawing has a crossing-free supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
