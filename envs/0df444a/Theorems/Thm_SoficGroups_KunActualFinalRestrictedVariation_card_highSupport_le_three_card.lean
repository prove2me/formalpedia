-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_card_highSupport_le_three_card
-- name    : SoficGroups.KunActualFinalRestrictedVariation.card_highSupport_le_three_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/97f232b1-8092-4bf1-894d-06f6b503c9b9
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.card_highSupport_le_three_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.card_highSupport_le_three_card
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (((Finset.univ.filter fun x : V =>
      (1 / 3 : ℝ) < f x).card : ℝ)) ≤ 3 * (T.card : ℝ) := by sorry
