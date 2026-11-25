-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_onto_of_irred
-- name    : PositivityTheory.ThK.SplitLoc.Unr.onto_of_irred
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:49.120244+00:00
-- url     : https://prove2.me/theorems/173bbbe4-66c0-402f-a3d2-a45a143dfb67
-- title:
--   Unr: onto of irred
-- statement:
--   The Unr construction uses the onto of irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1171-L1203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L1171-L1203

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

theorem PositivityTheory.ThK.SplitLoc.Unr.onto_of_irred (hI : IndIrred) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by sorry
