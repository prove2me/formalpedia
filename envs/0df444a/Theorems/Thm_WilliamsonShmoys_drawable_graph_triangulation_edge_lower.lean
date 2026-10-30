-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_triangulation_edge_lower
-- name    : WilliamsonShmoys.drawable_graph_triangulation_edge_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:53:52.026252+00:00
-- url     : https://prove2.me/theorems/360dfd46-ff48-420b-8199-ef7d5aad9824
-- title:
--   Drawable graph completion with planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_triangulation_edge_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
