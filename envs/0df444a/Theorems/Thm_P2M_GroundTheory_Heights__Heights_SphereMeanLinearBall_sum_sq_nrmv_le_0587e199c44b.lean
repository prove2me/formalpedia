-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:02.59495+00:00
-- url     : https://prove2.me/theorems/2f659526-98bf-4aa4-9f68-9f4696e28582
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq nrmv le 0587e199c44b: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq nrmv le 0587e199c44b
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq nrmv le 0587e199c44b construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball sum sq nrmv le 0587e199c44b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L21-L31

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«sum_sq_nrmv_le» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b
