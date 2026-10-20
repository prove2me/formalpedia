-- Prove2me | Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_sum_indicator_real_eq_mul_card
-- name    : SoficGroups.KunAdditiveMedianPoincare.sum_indicator_real_eq_mul_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/b31f04c6-a4d5-44fa-93fd-5b3660a0eae1
-- title:
--   SoficGroups.KunAdditiveMedianPoincare.sum_indicator_real_eq_mul_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunAdditiveMedianPoincare.sum_indicator_real_eq_mul_card
    {V : Type*} (A : Finset V)
    (q : V → Prop) [DecidablePred q] (m : ℝ) :
    (∑ x ∈ A, if q x then m else 0) =
      m * (A.filter q).card := by sorry
