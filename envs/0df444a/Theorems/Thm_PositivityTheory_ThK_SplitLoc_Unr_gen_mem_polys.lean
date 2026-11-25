-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gen_mem_polys
-- name    : PositivityTheory.ThK.SplitLoc.Unr.gen_mem_polys
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:23.495808+00:00
-- url     : https://prove2.me/theorems/a3d279ec-aa21-45dd-9475-f612bf22f3f2
-- title:
--   Unr: gen mem polys
-- statement:
--   The Unr construction uses the gen mem polys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L60-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L60-L84

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
open PowerSeries

theorem PositivityTheory.ThK.SplitLoc.Unr.gen_mem_polys {n : ℕ} (γ : Fin n → ℂ) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, γ i ^ (a i - M)) * T (fun i => min (a i) M)) :
    (∏ i, (1 - C (γ i) * X)) * mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, T a) ∈ polys := by sorry
