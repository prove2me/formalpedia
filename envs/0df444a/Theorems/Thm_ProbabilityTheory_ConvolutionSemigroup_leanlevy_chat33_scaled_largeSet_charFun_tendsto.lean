-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_largeSet_charFun_tendsto
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_largeSet_charFun_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:49:24.135096+00:00
-- url     : https://prove2.me/theorems/802b7e2a-b71b-48a4-b06f-f2a27f536863
-- title:
--   Scaled complex large-jump characteristic-integrand limit
-- statement:
--   The scaled complex large-set characteristic-integrand integral converges by applying the already proven real large-set theorem to real and imaginary parts and recombining.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3683-L3772

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_largeSet_charFun_tendsto (S : ConvolutionSemigroup)
    {ρ : ℝ} (hρ : 0 < ρ) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)) := by sorry
