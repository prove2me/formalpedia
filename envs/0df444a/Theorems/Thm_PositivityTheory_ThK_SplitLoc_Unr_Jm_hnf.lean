-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_hnf
-- name    : PositivityTheory.ThK.SplitLoc.Unr.Jm_hnf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:19.236706+00:00
-- url     : https://prove2.me/theorems/f15bc5e2-b577-449d-bd02-baa41b2b1e83
-- title:
--   Unr: Jm hnf
-- statement:
--   The Unr construction uses the Jm hnf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L542-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L542-L573

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem PositivityTheory.ThK.SplitLoc.Unr.Jm_hnf {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (M : ℕ)
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x) :
    ∃ T : (Fin n → ℕ) → ℂ,
      (∀ a, T a = (∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ (a i - M)) * T (fun i => min (a i) M)) ∧
      (∀ m : ℤ, m < 0 → Jm n φ m = 0) ∧ ∀ t : ℕ, Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, T a := by sorry
