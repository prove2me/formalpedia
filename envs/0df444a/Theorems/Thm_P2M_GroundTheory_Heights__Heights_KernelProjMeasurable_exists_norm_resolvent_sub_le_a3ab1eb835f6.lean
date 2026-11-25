-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:56.687802+00:00
-- url     : https://prove2.me/theorems/98b3d75b-a66e-46bf-9ca4-856ef2cf1afb
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm resolvent sub le a3ab1eb835f6: P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm resolvent sub le a3ab1eb835
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm resolvent sub le a3ab1eb835f6 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm resolvent sub le a3ab1eb835f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L86-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L86-L115

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6 (A : E →L[ℂ] F) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«exists_norm_resolvent_sub_le» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6
