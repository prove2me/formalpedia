-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension
-- name    : WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:06:09.670576+00:00
-- url     : https://prove2.me/theorems/21f6bd5a-2122-42d2-8965-a1a414a7eb7f
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Every connected simple graph with at least three vertices and a packaged crossing-free drawing is a subgraph of a planar graph on the same vertex type having exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
