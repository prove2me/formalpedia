-- Prove2me | Theorems.Thm_SoficGroups_unitaryImages_inner_sq_mul_card_le
-- name    : SoficGroups.unitaryImages_inner_sq_mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/edadd806-e691-43f8-8730-1cdba9d5614d
-- title:
--   SoficGroups.unitaryImages_inner_sq_mul_card_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryImages_inner_sq_mul_card_le
    {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ι → H ≃ₗᵢ[ℂ] H) (a b : H)
    (hb : ∀ i : ι, U i b = b)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j →
      inner ℂ (U i a) (U j a) = 0) :
    (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2 ≤
      ‖a‖ ^ 2 * ‖b‖ ^ 2 := by sorry
