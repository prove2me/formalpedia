-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:26.458806+00:00
-- url     : https://prove2.me/theorems/2bd16ddb-da5f-4646-b540-a229bf0090e3
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of 771c24ca10eb: P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of 771c24ca10eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of 771c24ca10eb construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of 771c24ca10eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L36-L38

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

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«fsLog_pointOf» := P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
