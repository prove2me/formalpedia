-- Prove2me | Theorems.Thm_Statistics_information_inequality
-- name    : Statistics.information_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T23:54:53.009764+00:00
-- url     : https://prove2.me/theorems/f3c1d06d-33dd-42fe-a6da-a8ea92bcf517
-- title:
--   Information inequality: $\mathrm{Cov}(\delta,g)^2 \le \mathrm{Var}(\delta)\,\mathbb{E}[g^2]$
-- statement:
--   **The information inequality**, the analytic core of the Cramér–Rao bound. Let $\mu$ be a probability measure, let $\delta \in L^2(\mu)$ be a statistic and let $g \in L^2(\mu)$ be a *score*, i.e. a square-integrable function with $\mathbb{E}_\mu[g] = 0$. Then
--   $$\bigl(\mathbb{E}_\mu[\delta g]\bigr)^2 \;\le\; \operatorname{Var}_\mu(\delta)\,\mathbb{E}_\mu[g^2].$$
--   Equivalently $\operatorname{Cov}_\mu(\delta, g)^2 \le \operatorname{Var}_\mu(\delta)\operatorname{Var}_\mu(g)$: it is the Cauchy–Schwarz inequality applied to the centred statistic $\delta - \mathbb{E}_\mu[\delta]$ and the score $g$. In a differentiable statistical model with score $g = \partial_\theta \log p_\theta$ and an estimator $\delta$ whose expectation is differentiable with $\partial_\theta \mathbb{E}_\theta[\delta] = \mathbb{E}_\theta[\delta g]$, this is exactly the Cramér–Rao bound $\operatorname{Var}(\delta) \ge (\partial_\theta \mathbb{E}_\theta[\delta])^2 / I(\theta)$ with Fisher information $I(\theta) = \mathbb{E}_\theta[g^2]$. Stating it in this form isolates the inequality from the regularity conditions that justify differentiating under the integral sign, so it can be reused in any model where that interchange has been established separately.
-- source:
--   C. R. Rao, Information and the accuracy attainable in the estimation of statistical parameters, Bull. Calcutta Math. Soc. 37 (1945), 81-91; H. Cramér, Mathematical Methods of Statistics, Princeton University Press, 1946, Section 32.3 (the information inequality). Textbook form: E. L. Lehmann and G. Casella, Theory of Point Estimation, 2nd ed., Springer, 1998, Chapter 2, Theorem 5.15 and the covariance inequality (2.5.1).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped ENNReal NNReal

theorem Statistics.information_inequality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (δ g : Ω → ℝ)
    (hδ : MemLp δ 2 μ) (hg : MemLp g 2 μ) (hg0 : ∫ ω, g ω ∂μ = 0) :
    (∫ ω, δ ω * g ω ∂μ) ^ 2
      ≤ (∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ) * (∫ ω, (g ω) ^ 2 ∂μ) := by sorry
