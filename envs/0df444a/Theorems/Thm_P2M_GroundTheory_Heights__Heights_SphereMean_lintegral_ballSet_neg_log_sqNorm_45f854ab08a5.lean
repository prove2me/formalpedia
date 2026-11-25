-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:41.112952+00:00
-- url     : https://prove2.me/theorems/8ce516b9-bd10-547a-8ec4-8cff7b29b30b
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log sq Norm 45f854ab08a5: P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log sq Norm 45f854ab08a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log sq Norm 45f854ab08a5 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log sq Norm 45f854ab08a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L129-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L129-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5 (m : ℕ) :
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log (sqNorm x)) =
      ENNReal.ofReal (1 / (m + 1)) * volume (ballSet (m + 1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«lintegral_ballSet_neg_log_sqNorm» := P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5
