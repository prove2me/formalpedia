-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_normalizedReferenceCompletionError_tendsto_zero
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.normalizedReferenceCompletionError_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/9df375d0-5727-4762-9699-f3403e6c519f
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.normalizedReferenceCompletionError_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualFirstStageReferenceExpansion.normalizedReferenceCompletionError_tendsto_zero
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hdisagreement : Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        normalizedReferenceCompletionError (C n) (σref n) (σact n))
      atTop (nhds 0) := by sorry
