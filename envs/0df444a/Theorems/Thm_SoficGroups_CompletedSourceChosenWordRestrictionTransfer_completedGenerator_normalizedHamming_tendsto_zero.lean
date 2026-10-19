-- Prove2me | Theorems.Thm_SoficGroups_CompletedSourceChosenWordRestrictionTransfer_completedGenerator_normalizedHamming_tendsto_zero
-- name    : SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/2a9fcef7-405d-41c8-864a-e58b37b4b779
-- title:
--   SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_tendsto_zero
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

theorem SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → Equiv.Perm (V n))
    (Z : (n : ℕ) → Finset (V n))
    (τ : (n : ℕ) → Equiv.Perm {x : V n // x ∈ Z n})
    (hagrees : ∀ n, ∀ x : {x : V n // x ∈ Z n},
      σ n (x : V n) ∈ Z n →
        ((τ n x : {x : V n // x ∈ Z n}) : V n) =
          σ n (x : V n))
    (hdeleted : Tendsto
      (fun n => (((Finset.univ \ Z n).card : ℝ) / (Z n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (τ n) (completedRestriction (σ n) (Z n)))
      atTop (nhds 0) := by sorry
