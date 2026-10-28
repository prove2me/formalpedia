-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_no_drawable_extension
-- name    : WilliamsonShmoys.drawable_supergraph_with_no_drawable_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:48:27.454992+00:00
-- url     : https://prove2.me/theorems/89b64cf2-3a44-44b7-8eb8-7bc1b6ae615e
-- title:
--   Drawable supergraph with no drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_with_no_drawable_extension {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hCard : 3 ≤ Fintype.card V) : ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧ ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U := by sorry
