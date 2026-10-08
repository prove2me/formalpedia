-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_idle_time_mean
-- name    : QueueingFundamentals.Bounds.idle_time_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:38.772781+00:00
-- url     : https://prove2.me/theorems/8b2cae88-1a29-4384-b89a-44dd4fcc72ed
-- title:
--   Eqs. (7.3)–(7.4) — $W_q^{(n+1)} - X^{(n)} = W_q^{(n)} + U^{(n)}$ and $E[X] = -E[U] = 1/\lambda - 1/\mu$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$ and $E[S] = 1/\mu$ with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion $W_q^{(n+1)} = \max(0, W_q^{(n)} + U^{(n)})$, where $U^{(n)} = S^{(n)} - T^{(n)}$ and $W_q^{(n)}$, $S^{(n)}$, $T^{(n)}$ are independent. Put $X^{(n)} = -\min(0, W_q^{(n)} + U^{(n)})$.
--
--   1. Pathwise, for every realisation,
--   $$
--   W_q^{(n+1)} - X^{(n)} = W_q^{(n)} + U^{(n)}. \qquad (7.3)
--   $$
--   2. In steady state, with $W_q^{(n)} \sim \nu$,
--   $$
--   E[X] = -E[U] = \frac{1}{\lambda} - \frac{1}{\mu}. \qquad (7.4)
--   $$
--
--   $X$ is the idle gap before the next service starts. Its mean fixes the long-run fraction of time the server is idle, and (7.4) is the first of the moment relations behind the bounds of §7.1.
--
--   **Formalization Note** The expectations are integrals against the product law $\nu \otimes B \otimes A$ of $(W_q^{(n)}, S^{(n)}, T^{(n)})$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.330, Eqs. (7.1)–(7.4)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eqs. (7.1)–(7.4), p.330. For a stationary G/G/1 queue with `ρ = λ/μ < 1`: pathwise,
`W_q^{(n+1)} − X^{(n)} = W_q^{(n)} + U^{(n)}` (7.3); and in steady state
`E[X] = −E[U] = 1/λ − 1/μ` (7.4). -/
theorem idle_time_mean
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∀ w s t : ℝ, lindley w s t - idleX w s t = w + (s - t)) ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = -∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) ∧
    -∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) = 1 / lam - 1 / mu := by sorry

end QueueingFundamentals.Bounds
