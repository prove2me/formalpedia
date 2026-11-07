-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_integrable_sinc_kernel_from_min_integrable
-- name    : ProbabilityTheory.leanlevy_chat15_integrable_sinc_kernel_from_min_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:21:03.09832+00:00
-- url     : https://prove2.me/theorems/ef083fe8-32f0-4c40-bc93-4640fdaee954
-- title:
--   General sinc Fourier integrability from min-square envelope
-- statement:
--   The sinc-damped Fourier kernel is Bochner integrable under any measure with integrable min(1,x²), provided the ordinary pointwise sinc inequalities hold.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 226-241; isolate the exact integrable-min-square premise used by IsLevyMeasure in the source, avoiding direct import of a malformed Definition module.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_integrable_sinc_kernel_from_min_integrable
    {ν : MeasureTheory.Measure ℝ}
    (hint : MeasureTheory.Integrable (fun x : ℝ => min 1 (x ^ 2)) ν) (ξ : ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ 1 - Real.sinc x)
    (hbound : ∀ x : ℝ, 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2)) :
    MeasureTheory.Integrable
      (fun x => Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)) ν := by sorry
