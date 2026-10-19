-- Prove2me | Theorems.Thm_SoficGroups_CompletedSourceChosenWordRestrictionTransfer_completedGenerator_normalizedHamming_le_deleted
-- name    : SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_le_deleted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/0377c06c-4aa4-47c0-b42f-552d88ff39a1
-- title:
--   SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_le_deleted
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open scoped BigOperators

theorem SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (Z : Finset V)
    (τ : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      σ (x : V) ∈ Z →
        ((τ x : {x : V // x ∈ Z}) : V) = σ (x : V)) :
    SoficGroups.normalizedHamming
      τ (completedRestriction σ Z) ≤
        (((Finset.univ \ Z).card : ℝ) / Z.card) := by sorry
