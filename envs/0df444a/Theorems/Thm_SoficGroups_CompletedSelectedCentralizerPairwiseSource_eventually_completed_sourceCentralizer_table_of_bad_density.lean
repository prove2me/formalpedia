-- Prove2me | Theorems.Thm_SoficGroups_CompletedSelectedCentralizerPairwiseSource_eventually_completed_sourceCentralizer_table_of_bad_density
-- name    : SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_completed_sourceCentralizer_table_of_bad_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/ee865221-c9dd-43cf-8932-dec217e51ec8
-- title:
--   SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_completed_sourceCentralizer_table_of_bad_density
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

theorem SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_completed_sourceCentralizer_table_of_bad_density
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) /
            (Z n).card)
      atTop (nhds 0))
    (σZ : (n : ℕ) → ι →
      Equiv.Perm {x : V n // x ∈ Z n})
    (hσZ : ∀ n i (x : V n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((σZ n i ⟨x, hx⟩ :
          {x : V n // x ∈ Z n}) : V n) = σ n i x)
    (t : ℕ → ℕ)
    (ht : ∀ n,
      2 * Fintype.card ι *
        (sourceCompletionBad
          (σ n) (p n) F (Z n)).card ≤ t n) :
    ∀ᶠ n in atTop,
      (∀ a ∈ F, ∀ b ∈ F,
        5 * SoficGroups.permutationDistance
          (completedRestriction (p n (a * b)) (Z n))
          (completedRestriction (p n a) (Z n) *
            completedRestriction (p n b) (Z n)) ≤
          Fintype.card {x : V n // x ∈ Z n}) ∧
      (∀ a ∈ F, ∀ b ∈ F, a ≠ b →
        Fintype.card {x : V n // x ∈ Z n} <
          5 * SoficGroups.permutationDistance
            (completedRestriction (p n a) (Z n))
            (completedRestriction (p n b) (Z n))) ∧
      (∀ a ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
        SoficGroups.permutationCommutationDefect
          (σZ n) (completedRestriction (p n a) (Z n)) ≤
            t n) := by sorry
