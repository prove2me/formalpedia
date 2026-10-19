-- Prove2me | Theorems.Thm_SoficGroups_CompletedSelectedCentralizerPairwiseSource_eventually_five_mul_sourceCompletionBad_le_of_density
-- name    : SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_five_mul_sourceCompletionBad_le_of_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/bb134678-2b1a-4c6b-97c1-c2e644ca0f6b
-- title:
--   SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_five_mul_sourceCompletionBad_le_of_density
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSelectedCentralizerPairwiseSource
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise

theorem SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_five_mul_sourceCompletionBad_le_of_density
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      5 * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card ≤ (Z n).card := by sorry
