-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_expected_estimator_eq
-- name    : RogersSatchell.Unbiased.expected_estimator_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:29.890578+00:00
-- url     : https://prove2.me/theorems/6a3ac433-0292-4acc-a97f-81a11b029a35
-- title:
--   Eq. (3) — E[S_t(S_t − X_t) + I_t(I_t − X_t)] = σ²t for every drift c: the high–low–close estimator is unbiased
-- statement:
--   Let $B$ be a standard Brownian motion on a probability space $(\Omega,\mathcal F,P)$ with every sample path continuous, let $c\in\mathbb R$ and $\sigma\ge0$, and let $X_t=\sigma B_t+ct$ be the log-price, with running maximum $S_t=\sup_{0\le u\le t}X_u$ and running minimum $I_t=\inf_{0\le u\le t}X_u$. Then for every $t\ge 0$ the random variable $S_t(S_t-X_t)+I_t(I_t-X_t)$ is integrable and
--   $$E\big[S_t(S_t-X_t)+I_t(I_t-X_t)\big]=\sigma^2t.$$
--
--   At $t=1$ this says that the estimator $\hat\sigma^2\equiv S_1(S_1-X_1)+I_1(I_1-X_1)$ of display (2), built from a day's high, low and closing log-prices, is an unbiased estimator of $\sigma^2$. The right-hand side does not depend on the drift $c$, which is the point of the estimator: unlike the Garman–Klass estimator, it stays unbiased when $c\neq0$.
--
--   **Formalization Note** The expectation is a Bochner integral and integrability is part of the conclusion. "Standard Brownian motion" is Mathlib's `IsBrownianReal` (Gaussian finite-dimensional laws with covariance $\min(s,t)$ and almost surely continuous paths) together with the hypothesis that every path is continuous, the usual choice of a continuous version, which makes $S_t$ and $I_t$ attained maxima and minima.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 505, Eq. (3) (with Eq. (2)); proved in Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, display (3), p. 505: for Brownian motion with any drift `c`, any `σ ≥ 0` and
any `t ≥ 0`, `E[S_t(S_t − X_t) + I_t(I_t − X_t)] = σ²t`. At `t = 1` this says the estimator `σ̂²` of
display (2) is unbiased for `σ²`. -/
theorem expected_estimator_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)
      + runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, (runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)
      + runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) ∂P = σ ^ 2 * t := by sorry

end RogersSatchell.Unbiased
