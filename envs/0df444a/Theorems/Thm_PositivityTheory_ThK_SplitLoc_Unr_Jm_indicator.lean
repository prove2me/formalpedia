-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_indicator
-- name    : PositivityTheory.ThK.SplitLoc.Unr.Jm_indicator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:26.988571+00:00
-- url     : https://prove2.me/theorems/ed981d61-7395-5c9a-851b-b76338fa0119
-- title:
--   Unr: Jm indicator
-- statement:
--   The Unr construction uses the Jm indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L575-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L575-L603

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

theorem PositivityTheory.ThK.SplitLoc.Unr.Jm_indicator (n : ℕ) (t : ℕ) :
    Jm n (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) t =
      ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ a i := by sorry
