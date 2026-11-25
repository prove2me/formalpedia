-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_weight_639b4831e09d
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_weight_639b4831e09d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:19.44614+00:00
-- url     : https://prove2.me/theorems/da288327-f895-5b80-b155-9ef1ace56828
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integral disc log weight 639b4831e09d: P2 M Ground Theory Heights  Heights Sphere Mean integral disc log weight 639b4831e09d
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integral disc log weight 639b4831e09d construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integral disc log weight 639b4831e09d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L115-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L115-L138

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_weight_639b4831e09d (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m = -(harmonic (m + 1) : ℝ) / (4 * (m + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integral_disc_log_weight» := P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_weight_639b4831e09d
