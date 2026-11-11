-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_upperRamp_indicator_error_le_annulus
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_upperRamp_indicator_error_le_annulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:37:23.694212+00:00
-- url     : https://prove2.me/theorems/5e07b203-dad7-421f-8736-ebdc47053f4b
-- title:
--   Upper cutoff approximation error bounded by annulus cutoff
-- statement:
--   For a bounded continuous integrand, the difference between upper cutoff weighting and the true large-set indicator is controlled pointwise by M times the annulus ramp.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3395-L3430

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_upperRamp_indicator_error_le_annulus (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    |min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x -
      Set.indicator (largeSet ρ) g x| ≤ M * max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) := by sorry
