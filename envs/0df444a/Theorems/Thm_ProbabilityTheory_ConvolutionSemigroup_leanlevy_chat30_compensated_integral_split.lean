-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_compensated_integral_split
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_compensated_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:26:14.216964+00:00
-- url     : https://prove2.me/theorems/68f9049f-d5ab-49d8-9a42-a9abbb6efaae
-- title:
--   Partition the compensated Lévy exponent into ball, annulus and tail
-- statement:
--   Split the globally integrable compensated Lévy kernel across a finite small ball, annulus below one and the outer tail, respecting the indicator at one. This is source-exact Identity 4 of the pinned ψ-side algebra proof.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4900

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Complex Filter Topology
open ProbabilityTheory.ConvolutionSemigroup
open scoped NNReal ENNReal ComplexOrder

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_compensated_integral_split
    {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    (∫ x, levyCompensatedIntegrand ξ x ∂ν)
      = (∫ x in {x : ℝ | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν)
        + (∫ x in {x : ℝ | r ≤ |x| ∧ |x| < 1},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν)
        + (∫ x in largeSet 1, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν) := by sorry
