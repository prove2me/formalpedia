-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5
-- name    : P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:47.040252+00:00
-- url     : https://prove2.me/theorems/4c3eff40-a711-5a70-9b51-1a2024d5f44c
-- title:
--   P2 M Positivity Theory Th K Split Loc Unr p  inv a4fcdbc5adf5: P2 M Positivity Theory Th K Split Loc Unr p  inv a4fcdbc5adf5
-- statement:
--   The P2 M Positivity Theory Th K Split Loc Unr p  inv a4fcdbc5adf5 construction uses the P2 M Positivity Theory Th K Split Loc Unr p  inv a4fcdbc5adf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1345-L1359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1345-L1359

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

theorem P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5 (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) :
    ∀ Ψ ∈ SB _, ∀ g, pUnr' a a' ϖ ν α (omB ν α g 1 Ψ) = pUnr' a a' ϖ ν α Ψ := by sorry

alias «PositivityTheory».«ThK».«SplitLoc».«Unr».«p'_inv» := P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5
