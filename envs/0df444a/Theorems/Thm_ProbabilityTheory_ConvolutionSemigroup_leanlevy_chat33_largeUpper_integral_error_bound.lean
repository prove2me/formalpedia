-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeUpper_integral_error_bound
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:48:57.979216+00:00
-- url     : https://prove2.me/theorems/d8664085-c3b1-4b52-bfda-5642e0d22b80
-- title:
--   Integrated cutoff approximation error bounded by annulus integral
-- statement:
--   For a finite real measure, the error in integrating a bounded continuous function against a smooth upper cutoff versus the sharp large-set cutoff is at most M times the annulus cutoff integral.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3580-L3615

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_error_bound (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ) (hM : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    |∫ x, min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x ∂μ -
      ∫ x in largeSet ρ, g x ∂μ| ≤
      M * ∫ x, max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ∂μ := by sorry
