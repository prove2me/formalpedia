-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_norm_iterate_sub_le_sum_successive
-- name    : SoficGroups.KunRootedWordPower.norm_iterate_sub_le_sum_successive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/301a230b-f70a-4b09-a066-b97a2b146021
-- title:
--   SoficGroups.KunRootedWordPower.norm_iterate_sub_le_sum_successive
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v

theorem SoficGroups.KunRootedWordPower.norm_iterate_sub_le_sum_successive
    {E : Type*} [NormedAddCommGroup E]
    (F : E → E) (x : E) (k : ℕ) :
    ‖(F^[k]) x - x‖ ≤
      ∑ j ∈ Finset.range k,
        ‖(F^[j + 1]) x - (F^[j]) x‖ := by sorry
