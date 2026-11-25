-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Weakae_integrable_k
-- name    : PositivityTheory.Rg.BcB.E2.P.Weakae.integrable_k
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:52:34.087966+00:00
-- url     : https://prove2.me/theorems/a6dd6d35-69d7-46ae-a4ae-0b4332c2939e
-- title:
--   Weakae: integrable k
-- statement:
--   The Weakae construction uses the integrable k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Weakae.lean#L22-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Weakae.lean#L22-L48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Weakae
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Weakae
variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]

theorem PositivityTheory.Rg.BcB.E2.P.Weakae.integrable_k (m : Measure Y) [SFinite m] (ν : Measure S) [IsFiniteMeasure ν]
    (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (c : Y → ℂ) (hf : IsRep F f) (hc : AEStronglyMeasurable c m)
    (hint : ∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m ≠ ⊤) :
    Integrable (fun p : Y × S => c p.1 * conj (f p.1 p.2)) (m.prod ν) := by sorry
