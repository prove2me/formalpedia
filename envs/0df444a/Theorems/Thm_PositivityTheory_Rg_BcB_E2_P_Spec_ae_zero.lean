-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Spec_ae_zero
-- name    : PositivityTheory.Rg.BcB.E2.P.Spec.ae_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:58.85249+00:00
-- url     : https://prove2.me/theorems/700e5140-6706-5465-b21a-6898be8450ed
-- title:
--   Spec: ae zero
-- statement:
--   The Spec construction uses the ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/AeZero.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/AeZero.lean#L10-L15

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_AeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Spec

theorem PositivityTheory.Rg.BcB.E2.P.Spec.ae_zero {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] [ν.Regular] (u : S → ℝ) (hu : Continuous u) (h0 : ∀ s, 0 ≤ u s)
    (hi : ∫ s, (u s : ℂ) ∂ν = 0) : ∀ᵐ s ∂ν, u s = 0 := by sorry
