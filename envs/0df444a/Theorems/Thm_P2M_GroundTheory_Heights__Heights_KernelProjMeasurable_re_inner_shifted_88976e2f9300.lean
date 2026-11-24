-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_re_inner_shifted_88976e2f9300
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_re_inner_shifted_88976e2f9300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:26.323782+00:00
-- url     : https://prove2.me/theorems/7cc94870-abf8-4ffc-8938-bd404f235116
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable re inner shifted 88976e2f9300: P2 M Ground Theory Heights  Heights Kernel Proj Measurable re inner shifted 88976e2f9300
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable re inner shifted 88976e2f9300 construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable re inner shifted 88976e2f9300 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L19-L23

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_re_inner_shifted_88976e2f9300 (A : E →L[ℂ] F) (ε : ℝ) (u : E) :
    RCLike.re (inner ℂ u (shifted A ε u)) = ‖A u‖ ^ 2 + ε * ‖u‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«re_inner_shifted» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_re_inner_shifted_88976e2f9300
