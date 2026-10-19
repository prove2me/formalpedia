-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_subset_survivors
-- name    : SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_subset_survivors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/a76c2307-a96c-426a-b0a9-1402260189da
-- title:
--   SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_subset_survivors
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators

theorem SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_subset_survivors
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    SoficGroups.MatchedComponentCompletion.sourceCompletionBad
      σ p F Z ⊆ Z := by sorry
