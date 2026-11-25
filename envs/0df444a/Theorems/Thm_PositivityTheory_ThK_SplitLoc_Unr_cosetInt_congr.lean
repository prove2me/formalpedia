-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_cosetInt_congr
-- name    : PositivityTheory.ThK.SplitLoc.Unr.cosetInt_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:35.541292+00:00
-- url     : https://prove2.me/theorems/66993a9b-850e-43fc-9037-80bfb5cdc73a
-- title:
--   Unr: coset Int congr
-- statement:
--   The Unr construction uses the coset Int congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L522-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L522-L538

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

theorem PositivityTheory.ThK.SplitLoc.Unr.cosetInt_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} {M : ℕ}
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x)
    {B B' : Matrix (Fin n) (Fin n) 𝒪[k]} (h : ∀ i j, (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) ^ M ∣ B i j - B' i j) :
    cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B) = cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B') := by sorry
