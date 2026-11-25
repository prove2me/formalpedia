-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:28.673816+00:00
-- url     : https://prove2.me/theorems/77c24143-d81e-4156-a6a5-067831029d6e
-- title:
--   P2 M Ground Theory Heights  Heights KTheta integral exp sum sq 107f6dbe98ea: P2 M Ground Theory Heights  Heights KTheta integral exp sum sq 107f6dbe98ea
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta integral exp sum sq 107f6dbe98ea construction uses the P2 M Ground Theory Heights  Heights KTheta integral exp sum sq 107f6dbe98ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L23-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea (c : ℝ) :
    ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) = (√(π / c)) ^ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«integral_exp_sum_sq» := P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea
