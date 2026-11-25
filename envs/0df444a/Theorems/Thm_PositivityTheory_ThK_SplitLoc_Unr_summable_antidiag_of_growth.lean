-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_summable_antidiag_of_growth
-- name    : PositivityTheory.ThK.SplitLoc.Unr.summable_antidiag_of_growth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:01.566075+00:00
-- url     : https://prove2.me/theorems/548edd7c-ac73-48bc-b6b5-e5f17265325e
-- title:
--   Unr: summable antidiag of growth
-- statement:
--   The Unr construction uses the summable antidiag of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L839-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L839-L869

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
  [MeasurableSpace k] [BorelSpace k]

theorem PositivityTheory.ThK.SplitLoc.Unr.summable_antidiag_of_growth {n : ℕ} (Q : Fin n → ℝ) (hQ : ∀ i, 1 ≤ Q i) {r : ℝ} (hr : 0 ≤ r)
    (hrQ : ∀ i, r * Q i < 1) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, (Q i : ℂ) ^ (a i - M)) * T (fun i => min (a i) M)) :
    Summable fun t : ℕ => r ^ t * ‖∑ a ∈ Finset.piAntidiag Finset.univ t, T a‖ := by sorry
