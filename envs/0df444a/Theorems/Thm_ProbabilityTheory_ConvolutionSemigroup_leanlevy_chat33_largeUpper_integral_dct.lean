-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeUpper_integral_dct
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:43:17.931703+00:00
-- url     : https://prove2.me/theorems/c35fb670-f58c-4f6d-8139-16670bcda89a
-- title:
--   DCT of upper large-set cutoff against a Lévy measure
-- statement:
--   The source-exact upper smooth cutoffs multiplied by bounded continuous g have ν-integrals tending to the ν-integral of g over |x|≥rho, using finite Lévy tail at rho/2.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3454-L3493

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_dct (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, f n x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x) ∧
      Tendsto (fun n => ∫ x, f n x ∂ν) atTop
        (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by sorry
