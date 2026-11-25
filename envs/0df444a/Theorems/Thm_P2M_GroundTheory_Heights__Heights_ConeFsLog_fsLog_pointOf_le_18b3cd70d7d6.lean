-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_le_18b3cd70d7d6
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_le_18b3cd70d7d6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:29.535078+00:00
-- url     : https://prove2.me/theorems/d93fee02-1560-40dd-9818-fc5ec58ed11f
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of le 18b3cd70d7d6: P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of le 18b3cd70d7d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of le 18b3cd70d7d6 construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log fs Log point Of le 18b3cd70d7d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_le_18b3cd70d7d6 (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) ≤ max (Real.log (h.norm u)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«fsLog_pointOf_le» := P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_le_18b3cd70d7d6
