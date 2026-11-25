-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Weakae_lint_slice
-- name    : PositivityTheory.Rg.BcB.E2.P.Weakae.lint_slice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:52:26.366383+00:00
-- url     : https://prove2.me/theorems/f20127ba-f5f9-518b-b4ab-d2558ad7f723
-- title:
--   Weakae: lint slice
-- statement:
--   The Weakae construction uses the lint slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Weakae.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Weakae.lean#L14-L20

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

theorem PositivityTheory.Rg.BcB.E2.P.Weakae.lint_slice (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F) :
    ∫⁻ s, ‖f s‖ₑ ∂ν ≤ ‖F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by sorry
