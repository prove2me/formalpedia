-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_smul_mem
-- name    : RiemannMasullo.elementarySchwartzSubmodule_smul_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:54:18.392534+00:00
-- url     : https://prove2.me/theorems/2d96a527-ea1e-4c31-9980-e44ec17991c2
-- title:
--   Scalar multiplication preserves the elementary Schwartz condition
-- statement:
--   Every lifted derivative scales by the constant, so its weighted norm is bounded by the original bound times the norm of the constant.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L351-L355

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSubmodule_smul_mem (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)) :
    c • f ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by sorry

end RiemannMasullo
