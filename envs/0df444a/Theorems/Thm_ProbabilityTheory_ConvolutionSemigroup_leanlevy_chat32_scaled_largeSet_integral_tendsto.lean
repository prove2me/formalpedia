-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_scaled_largeSet_integral_tendsto
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_largeSet_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:04:19.399232+00:00
-- url     : https://prove2.me/theorems/9428956c-1a46-48a8-becc-0b73d857ade3
-- title:
--   Scaled large-set integral convergence
-- statement:
--   Scaled large-set integral convergence assuming scaled jump test convergence and Lévy boundary-null conditions.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3438-L3662

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_largeSet_integral_tendsto (S : ConvolutionSemigroup)
    {ρ : ℝ} (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ} (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by sorry
