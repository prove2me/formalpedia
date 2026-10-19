-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sq_le_card_of_unit_interval_mass
-- name    : SoficGroups.KunActualFinalRestrictedVariation.sum_sq_le_card_of_unit_interval_mass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/97761028-7064-4dc0-b450-3ff0a8760c87
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.sum_sq_le_card_of_unit_interval_mass
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.sum_sq_le_card_of_unit_interval_mass
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ x : V, f x ^ 2) ≤ (T.card : ℝ) := by sorry
