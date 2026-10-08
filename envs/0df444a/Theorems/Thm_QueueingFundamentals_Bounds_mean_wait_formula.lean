-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_mean_wait_formula
-- name    : QueueingFundamentals.Bounds.mean_wait_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:45.294989+00:00
-- url     : https://prove2.me/theorems/65eb7c45-8a86-4e64-93fe-95e2698ae60e
-- title:
--   Eq. (7.7) — $W_q = (E[X^2] - E[U^2])/(2E[U])$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$ and $E[S] = 1/\mu$ with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion (7.1), let $U = S - T$, and let $X = -\min(0, W_q + U)$ with $W_q \sim \nu$, $S$ and $T$ independent.
--
--   Then the stationary line delay has a finite mean $W_q = E[W_q^{(n)}]$, and
--   $$
--   W_q = \frac{E[X^2] - E[U^2]}{2E[U]}. \qquad (7.7)
--   $$
--
--   This expresses the mean wait of a stable G/G/1 queue through second moments of $U$ and of the idle gap $X$. The upper bound (7.13) and the lower bound (7.14) are both read off from it.
--
--   **Formalization Note** The finiteness of $W_q$ is part of the conclusion, not a hypothesis. No finite second moment of the stationary wait is assumed, although the book's derivation squares (7.3). $E[U] = 1/\mu - 1/\lambda < 0$, so the denominator is nonzero.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.331, Eq. (7.7)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.7), p.331. For a stationary G/G/1 queue with `ρ < 1`, the stationary line delay has
finite mean `W_q = E[W_q^{(n)}]` and `W_q = (E[X²] − E[U²]) / (2E[U])`. -/
theorem mean_wait_formula
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν =
      (∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) - ∫ p, (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A)) /
        (2 * ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A)) := by sorry

end QueueingFundamentals.Bounds
