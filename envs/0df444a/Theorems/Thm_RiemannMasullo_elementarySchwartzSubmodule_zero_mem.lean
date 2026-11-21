-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_zero_mem
-- name    : RiemannMasullo.elementarySchwartzSubmodule_zero_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:54:13.055146+00:00
-- url     : https://prove2.me/theorems/0a82511e-3611-425a-ba63-289b20a0fa76
-- title:
--   The zero function satisfies the elementary Schwartz bounds
-- statement:
--   All mixed derivatives of the zero function vanish, so all weighted bounds are zero.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L335-L338

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}

namespace RiemannMasullo

theorem elementarySchwartzSubmodule_zero_mem :
    (0 : ElementaryLieGroup m n r F → ℂ) ∈
      {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
        ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)} := by sorry

end RiemannMasullo
