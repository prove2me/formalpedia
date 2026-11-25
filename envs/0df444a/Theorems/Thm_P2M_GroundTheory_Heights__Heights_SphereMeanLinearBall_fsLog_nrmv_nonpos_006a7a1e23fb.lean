-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_fsLog_nrmv_nonpos_006a7a1e23fb
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_fsLog_nrmv_nonpos_006a7a1e23fb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:10.162942+00:00
-- url     : https://prove2.me/theorems/377ef9d7-b8ae-5e96-9c3f-702c4055989a
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball fs Log nrmv nonpos 006a7a1e23fb: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball fs Log nrmv nonpos 006a7a1e23fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball fs Log nrmv nonpos 006a7a1e23fb construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball fs Log nrmv nonpos 006a7a1e23fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L45-L54

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_fsLog_nrmv_nonpos_006a7a1e23fb (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«fsLog_nrmv_nonpos» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_fsLog_nrmv_nonpos_006a7a1e23fb
