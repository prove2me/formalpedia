-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__unit_84d39629c538
-- name    : P2M_PositivityTheory_ThK_SplitLoc_Unr_p__unit_84d39629c538
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:40.874668+00:00
-- url     : https://prove2.me/theorems/bc10d2ab-a2b9-5b1a-9b61-c925fc0cb3c0
-- title:
--   P2 M Positivity Theory Th K Split Loc Unr p  unit 84d39629c538: P2 M Positivity Theory Th K Split Loc Unr p  unit 84d39629c538
-- statement:
--   The P2 M Positivity Theory Th K Split Loc Unr p  unit 84d39629c538 construction uses the P2 M Positivity Theory Th K Split Loc Unr p  unit 84d39629c538 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1390-L1401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1390-L1401

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
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

theorem P2M_PositivityTheory_ThK_SplitLoc_Unr_p__unit_84d39629c538 (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hα : IsUnram α) :
    ∀ h ∈ KO k (Fin (a + a')), pUnr' a a' ϖ ν α (Set.indicator {Y : Matrix (Fin a') (Fin (a + a')) k | ∀ i j, Y i j ∈ 𝒪[k]} 1) h = 1 := by sorry

alias «PositivityTheory».«ThK».«SplitLoc».«Unr».«p'_unit» := P2M_PositivityTheory_ThK_SplitLoc_Unr_p__unit_84d39629c538
