-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:46.071226+00:00
-- url     : https://prove2.me/theorems/c025bf19-d724-4b50-bc33-1c5fa0d724c3
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std dual Norm 06ad3d73255e: P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std dual Norm 06ad3d73255e
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std dual Norm 06ad3d73255e construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Linear Ball std dual Norm 06ad3d73255e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanLinearBall.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanLinearBall».«std_dualNorm» := P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e
