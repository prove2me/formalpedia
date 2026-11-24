-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_inter
-- name    : PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_inter
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:12.338913+00:00
-- url     : https://prove2.me/theorems/d7af035a-df7e-46d6-ae89-9ba7f8e4599b
-- title:
--   Unr: Jm eq inter
-- statement:
--   The Unr construction uses the Jm eq inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L473-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L473-L479

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

theorem PositivityTheory.ThK.SplitLoc.Unr.Jm_eq_inter {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (m : ℤ) :
    Jm n φ m = ∫ g in dShell n m ∩ {g | ∀ i j, g.val i j ∈ 𝒪[k]}, φ g.val ∂haarVol (KO k (Fin n)) := by sorry
