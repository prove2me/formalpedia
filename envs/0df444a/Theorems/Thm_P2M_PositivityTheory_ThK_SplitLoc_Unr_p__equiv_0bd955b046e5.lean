-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__equiv_0bd955b046e5
-- name    : P2M_PositivityTheory_ThK_SplitLoc_Unr_p__equiv_0bd955b046e5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:02:33.908264+00:00
-- url     : https://prove2.me/theorems/bed7e14d-485f-55d2-ae28-4a5e56e7c8a7
-- title:
--   P2 M Positivity Theory Th K Split Loc Unr p  equiv 0bd955b046e5: P2 M Positivity Theory Th K Split Loc Unr p  equiv 0bd955b046e5
-- statement:
--   The P2 M Positivity Theory Th K Split Loc Unr p  equiv 0bd955b046e5 construction uses the P2 M Positivity Theory Th K Split Loc Unr p  equiv 0bd955b046e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1368-L1373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1368-L1373

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

theorem P2M_PositivityTheory_ThK_SplitLoc_Unr_p__equiv_0bd955b046e5 : ∀ Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ, ∀ h₁,
    pUnr' a a' ϖ ν α (omB ν α 1 h₁ Ψ) = rtr h₁ (pUnr' a a' ϖ ν α Ψ) := by sorry

alias «PositivityTheory».«ThK».«SplitLoc».«Unr».«p'_equiv» := P2M_PositivityTheory_ThK_SplitLoc_Unr_p__equiv_0bd955b046e5
