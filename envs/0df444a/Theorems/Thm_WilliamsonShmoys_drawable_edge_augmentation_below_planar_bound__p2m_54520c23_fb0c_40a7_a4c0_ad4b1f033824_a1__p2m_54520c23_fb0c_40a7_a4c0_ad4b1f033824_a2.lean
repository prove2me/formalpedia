-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2
-- name    : WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:09.535264+00:00
-- url     : https://prove2.me/theorems/bf5da075-b040-4c21-a4f3-11149e96d4bb
-- title:
--   Drawable edge augmentation below the planar bound
-- statement:
--   Any drawable simple graph on at least three finite ordered vertices with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertices. This isolates the geometric augmentation and planar edge-count argument from the target’s short maximality contradiction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.edgeFinset.card) < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V, G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
