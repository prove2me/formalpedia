-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sum_comp_surj
-- name    : PositivityTheory.ThK.SplitLoc.Unr.sum_comp_surj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:28.196365+00:00
-- url     : https://prove2.me/theorems/9efc26e9-c3e1-47ff-b5d0-6a6f9c6cafd5
-- title:
--   Unr: sum comp surj
-- statement:
--   The Unr construction uses the sum comp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L367-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L367-L380

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
open GlobalTheory.SatakeBound

theorem PositivityTheory.ThK.SplitLoc.Unr.sum_comp_surj {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H] (π : G →+ H)
    (hπ : Function.Surjective π) {r : ℕ} (hr : Nat.card G = r * Nat.card H) (F : H → ℂ) :
    ∑ c, F (π c) = r * ∑ d, F d := by sorry
