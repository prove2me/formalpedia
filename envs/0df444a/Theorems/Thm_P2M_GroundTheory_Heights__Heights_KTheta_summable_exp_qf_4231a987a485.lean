-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:18.935907+00:00
-- url     : https://prove2.me/theorems/e65a9310-1f40-424a-a965-aadb7e0b26a4
-- title:
--   P2 M Ground Theory Heights  Heights KTheta summable exp qf 4231a987a485: P2 M Ground Theory Heights  Heights KTheta summable exp qf 4231a987a485
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta summable exp qf 4231a987a485 construction uses the P2 M Ground Theory Heights  Heights KTheta summable exp qf 4231a987a485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L69-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L69-L89

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

theorem P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485 (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) (hc : 0 < c)
    (v : Fin g → ℝ) : Summable fun k : Fin g → ℤ => exp (-c * qf Y (intVec k + v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«summable_exp_qf» := P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485
