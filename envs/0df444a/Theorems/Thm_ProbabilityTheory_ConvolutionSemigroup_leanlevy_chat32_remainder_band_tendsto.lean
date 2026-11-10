-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_remainder_band_tendsto
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_remainder_band_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T00:16:20.3822+00:00
-- url     : https://prove2.me/theorems/9b2e6f18-8d1a-4cf7-aa4a-57131750eed7
-- title:
--   Scaled cubic remainder annulus limit
-- statement:
--   Convergence of complex Taylor remainder integrals on a fixed Lévy annulus, following from the scalar band convergence lemma.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4160-L4250

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_remainder_band_tendsto (S : ConvolutionSemigroup)
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_δ : ν {x | |x| = δ} = 0) (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by sorry
