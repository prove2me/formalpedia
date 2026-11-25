-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_continuous_resolvent_11f38efbcd4f
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_continuous_resolvent_11f38efbcd4f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:41.783182+00:00
-- url     : https://prove2.me/theorems/4dff7ea2-31e9-4acf-9c5c-dc4a23b2a13c
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable continuous resolvent 11f38efbcd4f: P2 M Ground Theory Heights  Heights Kernel Proj Measurable continuous resolvent 11f38efbcd4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable continuous resolvent 11f38efbcd4f construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable continuous resolvent 11f38efbcd4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L125-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L125-L138

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_continuous_resolvent_11f38efbcd4f {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«continuous_resolvent» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_continuous_resolvent_11f38efbcd4f
