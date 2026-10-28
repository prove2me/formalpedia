-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_extension_792d6233_0413_48c2_8c4d_fb4d15268d51
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_extension_792d6233_0413_48c2_8c4d_fb4d15268d51
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:42:34.630317+00:00
-- url     : https://prove2.me/theorems/3d599ebf-15d4-4b04-8e7e-aa3198134bc8
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph with no strictly larger drawable supergraph on that same vertex type. Prove it by maximizing the edge count over drawable supergraphs of W. Drawing data restricts to subgraphs, and strict edge inclusion increases the count. This child removes only the finite maximal-choice step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_extension_792d6233_0413_48c2_8c4d_fb4d15268d51
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
        ∀ Y : SimpleGraph V, X ≤ Y →
          WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X := by
  sorry
