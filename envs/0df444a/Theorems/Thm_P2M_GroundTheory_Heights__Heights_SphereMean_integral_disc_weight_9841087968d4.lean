-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:26.705808+00:00
-- url     : https://prove2.me/theorems/92ddf55c-09fb-4f4c-8b0a-156cbd124f3f
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integral disc weight 9841087968d4: P2 M Ground Theory Heights  Heights Sphere Mean integral disc weight 9841087968d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integral disc weight 9841087968d4 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integral disc weight 9841087968d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L94-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L94-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4 (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ m = 1 / (2 * ((m : ℝ) + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integral_disc_weight» := P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4
