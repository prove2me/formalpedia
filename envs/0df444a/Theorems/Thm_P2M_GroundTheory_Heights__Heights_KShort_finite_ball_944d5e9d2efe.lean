-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe
-- name    : P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:33.272033+00:00
-- url     : https://prove2.me/theorems/08c4aa62-99db-43c8-bf28-9378cf1adc9e
-- title:
--   P2 M Ground Theory Heights  Heights KShort finite ball 944d5e9d2efe: P2 M Ground Theory Heights  Heights KShort finite ball 944d5e9d2efe
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort finite ball 944d5e9d2efe construction uses the P2 M Ground Theory Heights  Heights KShort finite ball 944d5e9d2efe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L121-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] (r : ℝ) :
    {v | v ∈ L ∧ ‖v‖ ≤ r}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«finite_ball» := P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe
