-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_charFun_sub_one_div_decomp
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_charFun_sub_one_div_decomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:46:08.24264+00:00
-- url     : https://prove2.me/theorems/4a560080-a0d3-4d10-95d9-5caaceb77981
-- title:
--   Split the scaled characteristic-function increment into drift and jump terms
-- statement:
--   Source-exact per-time decomposition of (charFun μ_t ξ − 1)/t into the small-ball linear term, compensated remainder and outer-jump term, for radius r ≤ 1. Required to assemble the Lévy–Khintchine exponent from its three independent limits.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3038-L3109

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open ProbabilityTheory.ConvolutionSemigroup
open scoped NNReal ENNReal ComplexOrder

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_charFun_sub_one_div_decomp (S : ProbabilityTheory.ConvolutionSemigroup) (t : {t : ℝ // 0 < t}) (ξ : ℝ)
    {r : ℝ} (hr1 : r ≤ 1) :
    (charFun (S.measure t : Measure ℝ) ξ - 1) / (↑t.val : ℂ) =
      (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
            ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1)
            ∂(S.measure t : Measure ℝ) := by sorry
