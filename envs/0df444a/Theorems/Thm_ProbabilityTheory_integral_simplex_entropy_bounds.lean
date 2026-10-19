-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_simplex_entropy_bounds
-- name    : ProbabilityTheory.integral_simplex_entropy_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:08:08.762495+00:00
-- url     : https://prove2.me/theorems/0f70a166-c407-45ef-854c-7ffbc47b2fba
-- title:
--   Entropy integral bounds for measurable finite simplex vectors
-- statement:
--   For a measurable finite probability vector almost everywhere under a probability measure, the integral of the sum of coordinate entropies lies between zero and the logarithm of the number of coordinates. The pointwise entropy inequalities include the singleton case; integrating them requires showing the entropy integrand is integrable.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory
open scoped BigOperators

theorem ProbabilityTheory.integral_simplex_entropy_bounds
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [Nonempty α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → α → ℝ)
    (hqMeas : ∀ a, Measurable (fun ω => q ω a))
    (hq0 : ∀ᵐ ω ∂P, ∀ a, 0 ≤ q ω a)
    (hq1 : ∀ᵐ ω ∂P, ∑ a : α, q ω a = 1) :
    0 ≤ MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ∧
      MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ≤
        Real.log (Fintype.card α : ℝ) := by sorry
