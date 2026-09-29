-- Prove2me | Theorems.Thm_Statistics_memLp_two_pi_prod
-- name    : Statistics.memLp_two_pi_prod
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:21.965301+00:00
-- url     : https://prove2.me/theorems/8527baef-ba61-4731-92d5-3c7cb50810c2
-- title:
--   A product of coordinatewise $L^2$ functions is $L^2$ on the product
-- statement:
--   **A product of coordinatewise $L^2$ functions is $L^2$ on the product.** Let $\mu$ be a probability measure and $\Psi \in L^2(\mu)$ measurable. Then on the $T$-fold product $\mu^{\otimes T}$ the function $p \mapsto \prod_{i<T} \Psi(p_i)$ lies in $L^2$, with
--   $$\int \Bigl(\prod_{i<T} \Psi(p_i)\Bigr)^2 \mathrm{d}\mu^{\otimes T}(p) \;=\; \Bigl(\int \Psi^2 \,\mathrm{d}\mu\Bigr)^{T} \;<\; \infty .$$
--   The point is that independence turns the square of a product into a product of squares, which factorizes. This is the envelope estimate that makes a product likelihood ratio square-integrable on a sample, so that it may be paired by Cauchy-Schwarz with an $L^2$ estimator.
-- source:
--   Standard consequence of independence; O. Kallenberg, Foundations of Modern Probability, 3rd ed., Springer, 2021, Chapter 8 (product measures and independence).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.memLp_two_pi_prod {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (Ψ : Ω → ℝ)
    (hΨmeas : Measurable Ψ) (hΨ : MemLp Ψ 2 μ) :
    MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 (Measure.pi fun _ : Fin T => μ) := by sorry
