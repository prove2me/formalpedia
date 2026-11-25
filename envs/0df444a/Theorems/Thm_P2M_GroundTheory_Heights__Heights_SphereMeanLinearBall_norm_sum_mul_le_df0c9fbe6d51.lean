-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:26.815873+00:00
-- url     : https://prove2.me/theorems/943eb5ec-759c-4d2b-b038-e57775be4dbf
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball norm sum mul le df0c9fbe6d51: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball norm sum mul le df0c9fbe6d51
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball norm sum mul le df0c9fbe6d51 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball norm sum mul le df0c9fbe6d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L33-L37

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51 (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«norm_sum_mul_le» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51
