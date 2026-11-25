-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:22.096891+00:00
-- url     : https://prove2.me/theorems/1ea3714b-cd87-4f76-ab3e-62f9d31823b8
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integral disc log pow 6b78cf6e0593: P2 M Ground Theory Heights  Heights Sphere Mean integral disc log pow 6b78cf6e0593
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integral disc log pow 6b78cf6e0593 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integral disc log pow 6b78cf6e0593 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L45-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593 (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integral_disc_log_pow» := P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_log_pow_6b78cf6e0593
