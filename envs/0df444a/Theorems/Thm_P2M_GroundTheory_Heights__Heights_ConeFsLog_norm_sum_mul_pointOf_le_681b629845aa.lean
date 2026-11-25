-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:09.747997+00:00
-- url     : https://prove2.me/theorems/829e84ac-bf1a-41dd-a582-822ba538f759
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log norm sum mul point Of le 681b629845aa: P2 M Ground Theory Heights  Heights Cone Fs Log norm sum mul point Of le 681b629845aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log norm sum mul point Of le 681b629845aa construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log norm sum mul point Of le 681b629845aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L29-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«norm_sum_mul_pointOf_le» := P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
