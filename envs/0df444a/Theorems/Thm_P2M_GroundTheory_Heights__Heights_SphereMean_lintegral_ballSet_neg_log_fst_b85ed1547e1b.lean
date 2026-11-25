-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:26.65241+00:00
-- url     : https://prove2.me/theorems/9e35ef02-55cf-44a4-96db-a0c2c9ae863c
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log fst b85ed1547e1b: P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log fst b85ed1547e1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log fst b85ed1547e1b construction uses the P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set neg log fst b85ed1547e1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L96-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L96-L117

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b (m : ℕ) :
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log ‖x 0‖) =
      ENNReal.ofReal (π * harmonic (m + 1) / (2 * (m + 1))) * volume (ballSet m 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«lintegral_ballSet_neg_log_fst» := P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b
