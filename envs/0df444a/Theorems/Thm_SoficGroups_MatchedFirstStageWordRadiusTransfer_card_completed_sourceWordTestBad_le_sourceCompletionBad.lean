-- Prove2me | Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_card_completed_sourceWordTestBad_le_sourceCompletionBad
-- name    : SoficGroups.MatchedFirstStageWordRadiusTransfer.card_completed_sourceWordTestBad_le_sourceCompletionBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/b66f0a63-e6e6-4aba-af5a-9e73a0040892
-- title:
--   SoficGroups.MatchedFirstStageWordRadiusTransfer.card_completed_sourceWordTestBad_le_sourceCompletionBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open Filter Topology
open scoped BigOperators

theorem SoficGroups.MatchedFirstStageWordRadiusTransfer.card_completed_sourceWordTestBad_le_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (P : Finset V) :
    (SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
      (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
        (σ i) P)
      (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
        (p j) P)
      F).card ≤
      (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        σ p F P).card := by sorry
