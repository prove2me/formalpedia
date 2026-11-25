-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_finite_of_polys
-- name    : PositivityTheory.ThK.SplitLoc.Unr.conv_finite_of_polys
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:41.476091+00:00
-- url     : https://prove2.me/theorems/5af702f4-39f0-4658-b4b1-fafb6c4d0fc0
-- title:
--   Unr: conv finite of polys
-- statement:
--   The Unr construction uses the conv finite of polys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L630-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L630-L642

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

theorem PositivityTheory.ThK.SplitLoc.Unr.conv_finite_of_polys {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0)
    (h : (P : PowerSeries ℂ) * PowerSeries.mk (fun s : ℕ => f s) ∈ polys) : (Function.support (conv P n f)).Finite := by sorry
