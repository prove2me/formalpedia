-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_annulusRamp_vanish_near_zero
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_annulusRamp_vanish_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:52:48.349106+00:00
-- url     : https://prove2.me/theorems/de49e0a9-c879-4ede-aa09-dd320904efa8
-- title:
--   Annulus cutoff vanishes near zero for indices at least two
-- statement:
--   For n≥2 the source-exact annulus ramp at radius rho is zero on a positive ball around the origin, so it is an admissible large-jump test function.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3278-L3303

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_annulusRamp_vanish_near_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 0 := by sorry
