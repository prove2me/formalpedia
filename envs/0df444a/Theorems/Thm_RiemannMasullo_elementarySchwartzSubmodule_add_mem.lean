-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_add_mem
-- name    : RiemannMasullo.elementarySchwartzSubmodule_add_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:54:07.235785+00:00
-- url     : https://prove2.me/theorems/fc83d372-55d4-44da-82e8-fffb77a8de2a
-- title:
--   Addition preserves the elementary Schwartz condition
-- statement:
--   The mixed derivative is additive on smooth functions, and the triangle inequality bounds each weighted derivative of a sum.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L341-L347

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSubmodule_add_mem {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞))
    (hg : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) :
    f + g ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by sorry

end RiemannMasullo
