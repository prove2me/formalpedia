-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020
-- name    : P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:38.215992+00:00
-- url     : https://prove2.me/theorems/f655b0c9-8bfe-49e8-b9b9-397295c48470
-- title:
--   P2 M Positivity Theory Th K Split Loc Unr p  mem 4c919705d020: P2 M Positivity Theory Th K Split Loc Unr p  mem 4c919705d020
-- statement:
--   The P2 M Positivity Theory Th K Split Loc Unr p  mem 4c919705d020 construction uses the P2 M Positivity Theory Th K Split Loc Unr p  mem 4c919705d020 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1290-L1322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1290-L1322

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

theorem P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020 (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hα : IsUnram α) :
    ∀ Ψ ∈ SB _, pUnr' a a' ϖ ν α Ψ ∈ indSp a a' α β := by sorry

alias «PositivityTheory».«ThK».«SplitLoc».«Unr».«p'_mem» := P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020
