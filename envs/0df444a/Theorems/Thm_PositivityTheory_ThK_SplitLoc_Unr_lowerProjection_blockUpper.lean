-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_lowerProjection_blockUpper
-- name    : PositivityTheory.ThK.SplitLoc.Unr.lowerProjection_blockUpper
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:23.915832+00:00
-- url     : https://prove2.me/theorems/cc790639-5f44-4322-9ba8-0b5b618fa9b0
-- title:
--   Unr: lower Projection block Upper
-- statement:
--   The Unr construction uses the lower Projection block Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1144-L1152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1144-L1152

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

theorem PositivityTheory.ThK.SplitLoc.Unr.lowerProjection_blockUpper {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dD : kˣ}
    (h2 : (dD : k) = (blkD b).det) :
    (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.val : Matrix (Fin a') (Fin (a + a')) k) =
      (blkDGL b dD h2).val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by sorry
