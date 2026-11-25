-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
-- name    : P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:13.721707+00:00
-- url     : https://prove2.me/theorems/7bef100c-0c16-4fd2-b888-3a6183f97c60
-- title:
--   P2 M Positivity Theory Th K Split Loc Unr p Unr  eq 5762b3186f8b: P2 M Positivity Theory Th K Split Loc Unr p Unr  eq 5762b3186f8b
-- statement:
--   The P2 M Positivity Theory Th K Split Loc Unr p Unr  eq 5762b3186f8b construction uses the P2 M Positivity Theory Th K Split Loc Unr p Unr  eq 5762b3186f8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1208-L1224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1208-L1224

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
variable {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

theorem P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ}
    (hΨ : Ψ ∈ SB _) (h : GL (Fin (a + a')) k) : pUnr' a a' ϖ ν α Ψ h = (α (gdet h) : ℂ) * apow (gdet h) ((a' : ℂ) / 2) *
      zetaUnr a' (a + a') ϖ ν (fun g => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k))) := by sorry

alias «PositivityTheory».«ThK».«SplitLoc».«Unr».«pUnr'_eq» := P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
