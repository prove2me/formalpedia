-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_vanish_lintegral_ball_smul
-- name    : ReciprocityTheory.L2DbarEstimates.I.vanish_lintegral_ball_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:47.984109+00:00
-- url     : https://prove2.me/theorems/d913a365-3924-5835-8761-c95798a7b0dc
-- title:
--   I: vanish lintegral ball smul
-- statement:
--   The I construction uses the vanish lintegral ball smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Vanish.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Vanish.lean#L10-L27

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.I.vanish_lintegral_ball_smul (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by sorry
