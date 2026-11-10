-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat31_drift_term
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat31_drift_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:38:00.23343+00:00
-- url     : https://prove2.me/theorems/4f69162e-27b2-4d78-ae38-da7dcd6cb846
-- title:
--   Scale-limited small-ball first moment contributes the Lévy drift term
-- statement:
--   For a sequence of times approaching zero with rescaled truncated first moment converging to b, the complex linear drift part of the characteristic-function expansion converges to b times frequency times i.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3000-L3034

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat31_drift_term
    (S : ProbabilityTheory.ConvolutionSemigroup) (ξ : ℝ) {r : ℝ}
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (_ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    {b : ℝ} (hb : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 b)) :
    Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
        ∫ x in {x | |x| < r}, (↑x * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 (↑b * ↑ξ * I)) := by sorry
