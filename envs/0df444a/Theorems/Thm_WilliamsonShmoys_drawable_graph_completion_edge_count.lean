-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_completion_edge_count
-- name    : WilliamsonShmoys.drawable_graph_completion_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:38:57.433724+00:00
-- url     : https://prove2.me/theorems/0a43870f-51b1-4bb4-b194-a179ddee1973
-- title:
--   Drawable graph completion with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices can be extended, without adding vertices, to a drawable graph with exactly three times the number of vertices minus six edges. The completion is obtained by augmenting the drawing to a triangulation; Euler’s formula gives its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
