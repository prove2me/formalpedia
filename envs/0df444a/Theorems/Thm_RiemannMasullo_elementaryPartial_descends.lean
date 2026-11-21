-- Prove2me | Theorems.Thm_RiemannMasullo_elementaryPartial_descends
-- name    : RiemannMasullo.elementaryPartial_descends
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:40:40.661934+00:00
-- url     : https://prove2.me/theorems/3745c080-c1d8-46a4-a810-e918e9f3efdd
-- title:
--   Smooth mixed derivatives descend under the elementary-group covering
-- statement:
--   For a smooth lifted fibre, every mixed coordinate partial is smooth and has the same value at any two lifts of a given elementary-group point.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L302-L307

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementaryPartial_descends (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) :
    ContDiff ℝ ∞ (fun xt ↦ elementaryPartial f β γ xt a b) ∧
      ∀ u v, elementaryCover u a b = elementaryCover v a b →
        elementaryPartial f β γ u a b = elementaryPartial f β γ v a b := by sorry

end RiemannMasullo
