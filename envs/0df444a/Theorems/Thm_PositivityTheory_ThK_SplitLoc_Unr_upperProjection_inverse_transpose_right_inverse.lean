-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_inverse_transpose_right_inverse
-- name    : PositivityTheory.ThK.SplitLoc.Unr.upperProjection_inverse_transpose_right_inverse
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:12.869924+00:00
-- url     : https://prove2.me/theorems/d9b16cc5-8ba4-4969-ab56-8861ff063d04
-- title:
--   Unr: upper Projection inverse transpose right inverse
-- statement:
--   The Unr construction uses the upper Projection inverse transpose right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1156-L1159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1156-L1159

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.ThK.SplitLoc.Unr.upperProjection_inverse_transpose_right_inverse {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val : Matrix (Fin a) (Fin (a + a')) k) *
      (h.valᵀ * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))ᵀ) = 1 := by sorry
