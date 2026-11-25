-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:43.728326+00:00
-- url     : https://prove2.me/theorems/ad392226-dce0-4b03-917e-b7d934006b8d
-- title:
--   P2 M Ground Theory Heights  Heights Log Int abs log inv pow mul le a3d1760957f0: P2 M Ground Theory Heights  Heights Log Int abs log inv pow mul le a3d1760957f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int abs log inv pow mul le a3d1760957f0 construction uses the P2 M Ground Theory Heights  Heights Log Int abs log inv pow mul le a3d1760957f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L208-L216

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0 (N : ℝ) (hN : 0 ≤ N) (d : ℕ) (x : ℂ) :
    |Real.log ‖((N : ℂ)⁻¹) ^ d * x‖| ≤ d * |Real.log N| + |Real.log ‖x‖| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«abs_log_inv_pow_mul_le» := P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0
