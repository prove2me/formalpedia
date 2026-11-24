-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_indicator_int_mul
-- name    : PositivityTheory.ThK.SplitLoc.Unr.indicator_int_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:51.054453+00:00
-- url     : https://prove2.me/theorems/823c06f7-9fc6-429d-be42-3f3415a8020b
-- title:
--   Unr: indicator int mul
-- statement:
--   The Unr construction uses the indicator int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1021-L1034
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1021-L1034

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

theorem PositivityTheory.ThK.SplitLoc.Unr.indicator_int_mul {A B C : Type} [Fintype B] [Fintype C] [DecidableEq B] {M : Matrix B C k} {R : Matrix C B k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hR : ∀ i j, R i j ∈ 𝒪[k]) (hMR : M * R = 1) (g : Matrix A B k) :
    Set.indicator {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A C k → ℂ) (g * M) =
      Set.indicator {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A B k → ℂ) g := by sorry
