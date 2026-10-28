-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph_edge_count
-- name    : WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:30:53.875795+00:00
-- url     : https://prove2.me/theorems/da8252b8-2352-4f59-ae85-03797958f126
-- title:
--   A drawable graph has a triangulating supergraph with Euler edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V, K ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
