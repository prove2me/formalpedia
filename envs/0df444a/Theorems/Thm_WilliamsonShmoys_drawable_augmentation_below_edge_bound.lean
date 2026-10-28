-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_augmentation_below_edge_bound
-- name    : WilliamsonShmoys.drawable_augmentation_below_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:44:44.01515+00:00
-- url     : https://prove2.me/theorems/e2343c2d-0f43-4111-a032-a621f715da94
-- title:
--   Augmenting a drawable graph below the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3|V|−6 edges has a proper drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_augmentation_below_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by sorry
