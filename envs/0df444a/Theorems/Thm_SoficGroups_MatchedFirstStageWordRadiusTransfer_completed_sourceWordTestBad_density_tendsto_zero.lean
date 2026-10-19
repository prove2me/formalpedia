-- Prove2me | Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_completed_sourceWordTestBad_density_tendsto_zero
-- name    : SoficGroups.MatchedFirstStageWordRadiusTransfer.completed_sourceWordTestBad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/3974ac72-a38f-4eaa-9712-9ca3419f3ba8
-- title:
--   SoficGroups.MatchedFirstStageWordRadiusTransfer.completed_sourceWordTestBad_density_tendsto_zero
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

theorem SoficGroups.MatchedFirstStageWordRadiusTransfer.completed_sourceWordTestBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (P E : (n : ℕ) → Finset (V n))
    (hcapture : ∀ n,
      SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆ P n ∩ E n)
    (hradius : Tendsto
      (fun n => (((P n ∩ E n).card : ℝ) / (P n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
          (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card : ℝ) / (P n).card)
      atTop (nhds 0) := by sorry
