-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a
-- name    : P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:39.136963+00:00
-- url     : https://prove2.me/theorems/40356d66-96ad-438e-b51a-427777a4c116
-- title:
--   P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm le norm shifted e469ac1e280a: P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm le norm shifted e469ac1e280a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm le norm shifted e469ac1e280a construction uses the P2 M Ground Theory Heights  Heights Kernel Proj Measurable exists norm le norm shifted e469ac1e280a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L55-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean#L55-L81

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

theorem P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KernelProjMeasurable».«exists_norm_le_norm_shifted» := P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a
