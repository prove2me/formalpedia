-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_sourceCompletionBad_le_deleted_add_wordBad
-- name    : SoficGroups.MatchedComponentExitBudget.card_sourceCompletionBad_le_deleted_add_wordBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/1a9f47fa-341f-46e0-9872-a7c12a83dc3c
-- title:
--   SoficGroups.MatchedComponentExitBudget.card_sourceCompletionBad_le_deleted_add_wordBad
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

theorem SoficGroups.MatchedComponentExitBudget.card_sourceCompletionBad_le_deleted_add_wordBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
      σ p F Z).card ≤
        (Fintype.card ι +
          (SoficGroups.CompressionCriterion.productTrackedTable F).card +
          Fintype.card ι *
            (SoficGroups.CompressionCriterion.productTrackedTable F).card) *
          (Finset.univ \ Z).card +
        (sourceWordTestBad σ p F).card := by sorry
