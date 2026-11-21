-- Prove2me | Theorems.Thm_RiemannMasullo_elementaryPartial_zero
-- name    : RiemannMasullo.elementaryPartial_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:38:44.383185+00:00
-- url     : https://prove2.me/theorems/b92a8b2e-70a4-47d5-b891-d308ec86d6dd
-- title:
--   The zeroth mixed derivative on the elementary cover
-- statement:
--   At multi-index zero the lifted mixed partial equals the value of the original function at the covered point.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L296-L298

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementaryPartial_zero (f : ElementaryLieGroup m n r F → ℂ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial f 0 0 xt a b = f (elementaryCover xt a b) := by sorry

end RiemannMasullo
