-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:34.176985+00:00
-- url     : https://prove2.me/theorems/cb87bedd-817c-53b9-b86b-8f44e85e8690
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable inner shifted of apply eq zero 645ecad0c612: P2 M Ground Theory Heights  Heights Kernel Proj Measurable inner shifted of apply eq zero 645eca
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable inner shifted of apply eq zero 645ecad0c612 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable inner shifted of apply eq zero 645ecad0c612 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ContinuousLinearMap
noncomputable section
open GroundTheory.Heights₂.Heights.KernelProjMeasurable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612 (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«inner_shifted_of_apply_eq_zero» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612
