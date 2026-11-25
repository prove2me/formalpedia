-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:31.00328+00:00
-- url     : https://prove2.me/theorems/7b049198-66ca-41fe-9710-d98d7abf36ad
-- title:
--   P2 M Ground Theory Heights  Heights KTheta integral exp qf b8e3fb58d743: P2 M Ground Theory Heights  Heights KTheta integral exp qf b8e3fb58d743
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta integral exp qf b8e3fb58d743 construction uses the P2 M Ground Theory Heights  Heights KTheta integral exp qf b8e3fb58d743 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L44-L56

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

theorem P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743 (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) :
    ∫ v, exp (-c * qf Y v) = (√(π / c)) ^ g * (√Y.det)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«integral_exp_qf» := P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743
