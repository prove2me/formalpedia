-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2
-- name    : WilliamsonShmoys.drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:46:51.557284+00:00
-- url     : https://prove2.me/theorems/44b3e4a1-3366-4047-b54d-bdbe1bcd0716
-- title:
--   Drawable graph extends to a triangulated edge-maximal graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. The extension can be obtained by adding noncrossing edges to triangulate the embedding; Euler’s formula then gives the edge count. In the parent, maximality identifies this extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
