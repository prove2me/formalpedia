-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_tendsto_resolvent_de8987e0176b
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_tendsto_resolvent_de8987e0176b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:02.076842+00:00
-- url     : https://prove2.me/theorems/1f24a1ed-ac32-4771-9b6e-7ba09ce9dfbe
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable tendsto resolvent de8987e0176b: P2 M Ground Theory Heights  Heights Kernel Proj Measurable tendsto resolvent de8987e0176b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable tendsto resolvent de8987e0176b construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable tendsto resolvent de8987e0176b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L117-L123

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_tendsto_resolvent_de8987e0176b (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«tendsto_resolvent» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_tendsto_resolvent_de8987e0176b
