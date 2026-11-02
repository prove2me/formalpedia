-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1
-- name    : WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:46.45272+00:00
-- url     : https://prove2.me/theorems/2a39e31c-7351-407d-8502-3f65a02c7380
-- title:
--   Drawable edge augmentation below the planar bound
-- statement:
--   A drawable simple graph on at least three finite ordered vertices with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertex set. The child isolates the planar augmentation step; the target follows by applying maximality to the supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : (letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card) < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V, G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
