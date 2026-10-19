-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_sum_geometric_budget_le
-- name    : SoficGroups.KunRootedWordPower.sum_geometric_budget_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/4a08acac-187e-4ccb-8aff-ae8dd4adfc76
-- title:
--   SoficGroups.KunRootedWordPower.sum_geometric_budget_le
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

theorem SoficGroups.KunRootedWordPower.sum_geometric_budget_le
    (q : ℝ) (hqzero : 0 ≤ q) (hqone : q < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      (q ^ j +
        (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹)) ≤
      2 / (1 - q) := by sorry
