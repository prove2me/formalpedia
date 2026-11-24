-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:28.304168+00:00
-- url     : https://prove2.me/theorems/1a80a2f3-4486-43c7-ba64-25c1cb651d7c
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable is Unit shifted 49b303e062a1: P2 M Ground Theory Heights  Heights Kernel Proj Measurable is Unit shifted 49b303e062a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable is Unit shifted 49b303e062a1 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable is Unit shifted 49b303e062a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L43-L53

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1 (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) : IsUnit (shifted A ε) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«isUnit_shifted» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1
