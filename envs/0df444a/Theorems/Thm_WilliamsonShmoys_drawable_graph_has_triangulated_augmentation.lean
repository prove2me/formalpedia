-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_augmentation
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:46:37.554231+00:00
-- url     : https://prove2.me/theorems/e9171c8e-e0b3-4464-9c0d-53f9e4fb34b7
-- title:
--   A drawable graph has a triangulated augmentation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
