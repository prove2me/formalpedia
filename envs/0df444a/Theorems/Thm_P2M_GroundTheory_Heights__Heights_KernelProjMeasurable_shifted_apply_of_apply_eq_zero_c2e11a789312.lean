-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:58.106897+00:00
-- url     : https://prove2.me/theorems/12eb6585-7ac7-4224-af92-7ebbc5bcd5bd
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable shifted apply of apply eq zero c2e11a789312: P2 M Ground Theory Heights  Heights Kernel Proj Measurable shifted apply of apply eq zero c2e11a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable shifted apply of apply eq zero c2e11a789312 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable shifted apply of apply eq zero c2e11a789312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L29-L31

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312 (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«shifted_apply_of_apply_eq_zero» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312
