-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:34.149413+00:00
-- url     : https://prove2.me/theorems/3d8c3b10-60c0-49db-bbfb-7ed66a77d99b
-- title:
--   P2 M Ground Theory Heights  Heights KTheta integral exp two pi qf 7f0897f8e415: P2 M Ground Theory Heights  Heights KTheta integral exp two pi qf 7f0897f8e415
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta integral exp two pi qf 7f0897f8e415 construction uses the P2 M Ground Theory Heights  Heights KTheta integral exp two pi qf 7f0897f8e415 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L58-L67

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

theorem P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415 (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    ∫ v, exp (-(2 * π) * qf Y v) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«integral_exp_two_pi_qf» := P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415
