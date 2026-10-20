-- Prove2me | Theorems.Thm_SoficGroups_ComponentMidrankVariance_twice_lower_rank_pairs_add_equal_rank_pairs
-- name    : SoficGroups.ComponentMidrankVariance.twice_lower_rank_pairs_add_equal_rank_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/3e8f1e25-219f-4229-9851-64bed565229c
-- title:
--   SoficGroups.ComponentMidrankVariance.twice_lower_rank_pairs_add_equal_rank_pairs
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators

theorem SoficGroups.ComponentMidrankVariance.twice_lower_rank_pairs_add_equal_rank_pairs
    {V : Type*} (C : Finset V) (b : V → ℤ) :
    2 * (∑ x ∈ C, ((C.filter fun z => b z < b x).card : ℝ)) +
        (∑ x ∈ C, ((C.filter fun z => b z = b x).card : ℝ)) =
      (C.card : ℝ) ^ 2 := by sorry
