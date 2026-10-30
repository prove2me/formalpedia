-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion_same_vertices_v3
-- name    : WilliamsonShmoys.connected_planar_triangulation_completion_same_vertices_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:14:24.706839+00:00
-- url     : https://prove2.me/theorems/e5e61a9e-aae6-41b6-82c4-d73ea4490ad9
-- title:
--   Triangulation completion of a connected drawable graph
-- statement:
--   Every connected drawable simple graph with at least three vertices can be extended on the same vertices to a drawable graph with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_triangulation_completion_same_vertices_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
