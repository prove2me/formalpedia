-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_marchal_lower_bound
-- name    : QueueingFundamentals.Bounds.marchal_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:34:09.77082+00:00
-- url     : https://prove2.me/theorems/c8c230ef-a478-4eb6-83e2-f30e5b2ac224
-- title:
--   Eq. (7.14) — Marchal's lower bound $W_q \ge (\lambda^2\sigma_B^2 + \rho(\rho-2))/(2\lambda(1-\rho))$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$, $E[S] = 1/\mu$ and $\sigma_B^2 = \mathrm{Var}[S]$, with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion (7.1).
--
--   Then the mean stationary line delay $W_q$ is finite and
--   $$
--   W_q \ge \frac{\lambda^2\sigma_B^2 + \rho(\rho - 2)}{2\lambda(1 - \rho)}. \qquad (7.14)
--   $$
--
--   This is the lower bound of Marchal (1978), valid for every stationary G/G/1 queue with $\rho < 1$. It is positive exactly when $\sigma_B^2 > (2 - \rho)/(\lambda\mu)$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.333, Eq. (7.14)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.14), p.333 (Marchal's lower bound). For every stationary G/G/1 queue with
`ρ = λ/μ < 1`, the stationary line delay has finite mean and
`W_q ≥ (λ²σ_B² + ρ(ρ − 2)) / (2λ(1 − ρ))`. -/
theorem marchal_lower_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    (lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu)) ≤
      meanWait ν := by sorry

end QueueingFundamentals.Bounds
