-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_kingman_upper_bound
-- name    : QueueingFundamentals.Bounds.kingman_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:34:41.169993+00:00
-- url     : https://prove2.me/theorems/c8fff77b-dc59-479b-b782-db0a5dfd5e3c
-- title:
--   Eq. (7.13) — Kingman's bound $W_q \le \lambda(\sigma_A^2 + \sigma_B^2)/(2(1-\rho))$ for the G/G/1 queue
-- statement:
--   Consider a single-server G/G/1 queue. Its interarrival times $T^{(n)}$ are independent and identically distributed, nonnegative, with $E[T] = 1/\lambda$ and variance $\sigma_A^2 = \mathrm{Var}[T]$. Its service times $S^{(n)}$ are independent and identically distributed, nonnegative, with $E[S] = 1/\mu$ and variance $\sigma_B^2 = \mathrm{Var}[S]$. Both have finite second moments, $\lambda, \mu > 0$, the service and interarrival times are independent, and the traffic intensity satisfies
--   $$
--   \rho = \frac{\lambda}{\mu} < 1.
--   $$
--   The line delays follow Lindley's recursion $W_q^{(n+1)} = \max(0, W_q^{(n)} + S^{(n)} - T^{(n)})$. Suppose the queue is stationary: the law $\nu$ of $W_q^{(n)}$ is carried unchanged by one step of the recursion.
--
--   Then the mean stationary line delay $W_q = E[W_q^{(n)}]$ is finite and
--   $$
--   W_q \le \frac{\lambda(\sigma_A^2 + \sigma_B^2)}{2(1 - \rho)}. \qquad (7.13)
--   $$
--
--   This is Kingman's upper bound. It holds for every stationary G/G/1 queue with $\rho < 1$ and uses only the first two moments of the interarrival and service times. It is the standard worst-case estimate for single-server congestion.
--
--   **Formalization Note** Stationarity is invariance of the law of the line delay under Lindley's recursion, with $W_q^{(n)}$, $S^{(n)}$, $T^{(n)}$ independent. The finiteness of $W_q$ is part of the conclusion. No finite second moment of the stationary wait is assumed.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.333, Eq. (7.13)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.13), p.333 (Kingman's upper bound). For every stationary G/G/1 queue with
`ρ = λ/μ < 1`, the stationary line delay has finite mean and
`W_q ≤ λ(σ_A² + σ_B²) / (2(1 − ρ))`. -/
theorem kingman_upper_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν ≤ lam * (interarrivalVar A + serviceVar B) / (2 * (1 - lam / mu)) := by sorry

end QueueingFundamentals.Bounds
