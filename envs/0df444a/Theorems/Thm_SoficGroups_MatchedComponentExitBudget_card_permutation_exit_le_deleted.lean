-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_permutation_exit_le_deleted
-- name    : SoficGroups.MatchedComponentExitBudget.card_permutation_exit_le_deleted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/0417c254-4fb2-41d2-a05c-5782d80bc87f
-- title:
--   SoficGroups.MatchedComponentExitBudget.card_permutation_exit_le_deleted
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

theorem SoficGroups.MatchedComponentExitBudget.card_permutation_exit_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (Z : Finset V) :
    (Z.filter fun x => p x ∉ Z).card ≤
      (Finset.univ \ Z).card := by sorry
