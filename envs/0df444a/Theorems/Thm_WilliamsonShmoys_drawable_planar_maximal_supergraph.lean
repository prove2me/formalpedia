-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_planar_maximal_supergraph
-- name    : WilliamsonShmoys.drawable_planar_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:09:35.40297+00:00
-- url     : https://prove2.me/theorems/5c65706f-3038-4158-9cae-3087641d5cd0
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same vertex type that is inclusion-maximal among drawable supergraphs. This follows by choosing a maximal element among the finitely many graph extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_planar_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Z : SimpleGraph V, W ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ Y : SimpleGraph V, Z ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = Z := by sorry
