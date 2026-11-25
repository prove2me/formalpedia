-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:59.662065+00:00
-- url     : https://prove2.me/theorems/cec074d8-5526-434e-b044-2d6e16666427
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integrable disc pow fb93bb3ac09d: P2 M Ground Theory Heights  Heights Sphere Mean integrable disc pow fb93bb3ac09d
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integrable disc pow fb93bb3ac09d construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integrable disc pow fb93bb3ac09d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L59-L61

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integrable_disc_pow» := P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d
