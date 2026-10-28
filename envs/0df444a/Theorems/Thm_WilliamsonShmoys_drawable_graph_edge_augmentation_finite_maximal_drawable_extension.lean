-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_edge_augmentation_finite_maximal_drawable_extension
-- name    : WilliamsonShmoys.drawable_graph_edge_augmentation_finite_maximal_drawable_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:51:13.434505+00:00
-- url     : https://prove2.me/theorems/53cba3d9-9292-4f21-bbdc-7a909b49d410
-- title:
--   Finite maximal drawable extension for edge augmentation
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that vertex type that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_edge_augmentation_finite_maximal_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
        ∀ Z : SimpleGraph V, Y < Z → ¬ WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
