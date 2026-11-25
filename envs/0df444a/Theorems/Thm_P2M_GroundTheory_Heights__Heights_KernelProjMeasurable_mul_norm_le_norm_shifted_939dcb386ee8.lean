-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_mul_norm_le_norm_shifted_939dcb386ee8
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_mul_norm_le_norm_shifted_939dcb386ee8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:13.847078+00:00
-- url     : https://prove2.me/theorems/d213fbe7-41f2-49cb-bc29-362bebc24a51
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable mul norm le norm shifted 939dcb386ee8: P2 M Ground Theory Heights  Heights Kernel Proj Measurable mul norm le norm shifted 939dcb386ee8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable mul norm le norm shifted 939dcb386ee8 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable mul norm le norm shifted 939dcb386ee8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L33-L41

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_mul_norm_le_norm_shifted_939dcb386ee8 (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) (u : E) :
    ε * ‖u‖ ≤ ‖shifted A ε u‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«mul_norm_le_norm_shifted» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_mul_norm_le_norm_shifted_939dcb386ee8
