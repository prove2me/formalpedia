-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_band_of_largeSet_limits
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_band_of_largeSet_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:02:54.8742+00:00
-- url     : https://prove2.me/theorems/eb386522-83f4-4d81-9154-edd9047f6ec7
-- title:
--   Band convergence from two large-set limits
-- statement:
--   If two scaled large-set integrals converge at nested radii, the intervening annular-band integral converges by a disjoint set difference identity.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3776-L3842

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_band_of_largeSet_limits (S : ConvolutionSemigroup)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ}
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (hδlim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet δ, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in largeSet δ, g x ∂ν)))
    (hρlim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in largeSet ρ, g x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂ν)) := by sorry
