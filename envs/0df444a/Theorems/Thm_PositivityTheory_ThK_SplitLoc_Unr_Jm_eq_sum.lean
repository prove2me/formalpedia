-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_sum
-- name    : PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:27.990442+00:00
-- url     : https://prove2.me/theorems/7a96819f-7ff7-4093-afd3-69897aeeae6a
-- title:
--   Unr: Jm eq sum
-- statement:
--   The Unr construction uses the Jm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L495-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L495-L520

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible

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

theorem PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_sum {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : Continuous φ)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) [∀ a : Fin n → ℕ, Fintype (HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a)] (t : ℕ) :
    Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, ∑ c, cosetInt φ (hermGL hϖ.irreducible a c).val := by sorry
