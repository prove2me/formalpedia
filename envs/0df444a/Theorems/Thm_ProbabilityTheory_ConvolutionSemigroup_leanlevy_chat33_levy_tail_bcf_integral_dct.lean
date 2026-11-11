-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_levy_tail_bcf_integral_dct
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_integral_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:33:55.246822+00:00
-- url     : https://prove2.me/theorems/653e4340-8768-4ad9-be16-1406599596fc
-- title:
--   Dominated convergence for compactly supported bounded-continuous Lévy tails
-- statement:
--   A uniformly bounded bounded-continuous sequence, eventually supported outside a positive radius, has ν-integrals converging to its prescribed large-set indicator limit under a Lévy measure.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3454-L3538

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_integral_dct {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {ρ : ℝ} (hρ : 0 < ρ)
    (f : ℕ → BoundedContinuousFunction ℝ ℝ) (M : ℝ)
    (hf_bound : ∀ n x, |f (n + 1) x| ≤ M)
    (hf_support : ∀ n x, |x| < ρ → f (n + 1) x = 0)
    (g : ℝ → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop
      (𝓝 (Set.indicator (largeSet ρ) g x))) :
    Tendsto (fun n => ∫ x, f n x ∂ν) atTop
      (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by sorry
