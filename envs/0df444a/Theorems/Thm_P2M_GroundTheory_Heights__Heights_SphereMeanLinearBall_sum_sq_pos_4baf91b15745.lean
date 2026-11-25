-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_pos_4baf91b15745
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_pos_4baf91b15745
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:22.662837+00:00
-- url     : https://prove2.me/theorems/8275336c-1c3a-566c-8bb6-26201aca3d3e
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq pos 4baf91b15745: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq pos 4baf91b15745
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq pos 4baf91b15745 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq pos 4baf91b15745 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall
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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_pos_4baf91b15745 {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«sum_sq_pos» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_pos_4baf91b15745
