-- Prove2me | Theorems.Thm_SoficGroups_norm_finset_sum_sq_eq_of_pairwise_inner_zero
-- name    : SoficGroups.norm_finset_sum_sq_eq_of_pairwise_inner_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/cc39834d-8dde-419d-b31f-25fe4ae9482d
-- title:
--   SoficGroups.norm_finset_sum_sq_eq_of_pairwise_inner_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.norm_finset_sum_sq_eq_of_pairwise_inner_zero
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : ι → H) (s : Finset ι)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by sorry
