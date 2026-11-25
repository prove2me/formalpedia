-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:34.95638+00:00
-- url     : https://prove2.me/theorems/71e7dd29-74b5-4a70-b994-c0656a9cfbef
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log norm le of fs Log le 2952b5d2345d: P2 M Ground Theory Heights  Heights Cone Fs Log norm le of fs Log le 2952b5d2345d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log norm le of fs Log le 2952b5d2345d construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log norm le of fs Log le 2952b5d2345d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L53-L64

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

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«norm_le_of_fsLog_le» := P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d
