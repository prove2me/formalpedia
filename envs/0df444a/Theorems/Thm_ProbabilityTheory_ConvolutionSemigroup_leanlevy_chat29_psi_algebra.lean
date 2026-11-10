-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat29_psi_algebra
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat29_psi_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:25:52.12084+00:00
-- url     : https://prove2.me/theorems/27c2debf-874d-4fe2-9cb3-fdf29bd79948
-- title:
--   Lévy-Khintchine ν-side algebra at an atom-free split radius
-- statement:
--   Algebraically reorganise the drift, small-ball Taylor remainder and large-jump integral into the radius-one Lévy-Khintchine exponent, retaining the radius-r variance correction. Source exact from the pinned upstream proof.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4749

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Complex Filter Topology
open ProbabilityTheory.ConvolutionSemigroup
open scoped NNReal ENNReal ComplexOrder

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat29_psi_algebra
    {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (b_r : ℝ) (σ_sq_r : ℝ≥0) :
    (↑b_r * ↑ξ * I
      + (-(↑(σ_sq_r : ℝ) * ↑ξ ^ 2 / 2)
          + ∫ x in {x | |x| < r},
              (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν))
      + ∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν =
    ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by sorry
