-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29
-- name    : P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:53.039408+00:00
-- url     : https://prove2.me/theorems/347a724a-6fa5-4fb1-96a7-2454b51d6c30
-- title:
--   P2 M Ground Theory Heights  Heights lin Form const mul b5306e01af29: P2 M Ground Theory Heights  Heights lin Form const mul b5306e01af29
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Form const mul b5306e01af29 construction uses the P2 M Ground Theory Heights  Heights lin Form const mul b5306e01af29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29 (c : ℂ) (v : Fin n → ℂ) :
    linForm (fun j => c * v j) = C c * linForm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linForm_const_mul» := P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29
