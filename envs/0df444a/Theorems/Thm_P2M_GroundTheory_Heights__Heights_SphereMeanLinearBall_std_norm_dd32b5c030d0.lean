-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_norm_dd32b5c030d0
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_norm_dd32b5c030d0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:44.313771+00:00
-- url     : https://prove2.me/theorems/e8a8869a-0bc9-4333-8cee-9ce7ed97a156
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std norm dd32b5c030d0: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std norm dd32b5c030d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std norm dd32b5c030d0 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std norm dd32b5c030d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L14-L15

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_norm_dd32b5c030d0 (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«std_norm» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_norm_dd32b5c030d0
