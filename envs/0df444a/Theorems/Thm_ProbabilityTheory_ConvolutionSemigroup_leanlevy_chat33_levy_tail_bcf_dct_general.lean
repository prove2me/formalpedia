-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_levy_tail_bcf_dct_general
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_dct_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:41:11.571348+00:00
-- url     : https://prove2.me/theorems/03d47d2c-3a6f-4d81-8b10-13e073e36716
-- title:
--   General finite-tail Lévy dominated convergence for bounded continuous sequences
-- statement:
--   For a Lévy measure, a uniformly bounded BCF sequence eventually vanishing inside a fixed ball has convergent integrals whenever it has a pointwise limit; the limit set may differ from the support radius.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3454-L3538

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_levy_tail_bcf_dct_general {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {r : ℝ} (hr : 0 < r)
    (f : ℕ → BoundedContinuousFunction ℝ ℝ) (M : ℝ)
    (hf_bound : ∀ n x, |f (n + 1) x| ≤ M)
    (hf_support : ∀ n x, |x| < r → f (n + 1) x = 0)
    (g : ℝ → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) := by sorry
