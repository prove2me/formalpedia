-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_two_sided_bounds
-- name    : QueueingFundamentals.Bounds.two_sided_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:34:32.619047+00:00
-- url     : https://prove2.me/theorems/eb560699-0b3c-447b-8b6d-9fa048512eca
-- title:
--   Eq. (7.17) — $\max(0, r_0, \text{Marchal}) \le W_q \le \lambda(\sigma_A^2 + \sigma_B^2)/(2(1-\rho))$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$, $E[S] = 1/\mu$, $\sigma_A^2 = \mathrm{Var}[T]$ and $\sigma_B^2 = \mathrm{Var}[S]$, with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion (7.1). Let $r_0$ be the nonnegative root of $f(z) = z - \int_{-z}^{\infty}[1 - U(t)]\,dt$, where $U(t)$ is the CDF of $U = S - T$.
--
--   Then $f$ has exactly one nonnegative root, the mean stationary line delay $W_q$ is finite, and
--   $$
--   \max\left(0,\ r_0,\ \frac{\lambda^2\sigma_B^2 + \rho(\rho - 2)}{2\lambda(1 - \rho)}\right) \le W_q \le \frac{\lambda(\sigma_A^2 + \sigma_B^2)}{2(1 - \rho)}. \qquad (7.17)
--   $$
--
--   This combines Kingman's upper bound (7.13), Marchal's lower bound (7.14) and the bound $W_q \ge r_0$ into one two-sided estimate.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.336, Eq. (7.17)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.17), p.336. For a stationary G/G/1 queue with `ρ < 1`, with `r₀` the unique
nonnegative root of `f(z) = z − ∫_{−z}^{∞} [1 − U(t)] dt`:
`max(0, r₀, (λ²σ_B² + ρ(ρ − 2))/(2λ(1 − ρ))) ≤ W_q ≤ λ(σ_A² + σ_B²)/(2(1 − ρ))`. -/
theorem two_sided_bounds
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∃! r : ℝ, 0 ≤ r ∧ rootFun A B r = 0) ∧
    Integrable (fun w : ℝ => w) ν ∧
    ∀ r : ℝ, 0 ≤ r → rootFun A B r = 0 →
      max (max 0 r)
          ((lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu))) ≤
        meanWait ν ∧
      meanWait ν ≤ lam * (interarrivalVar A + serviceVar B) / (2 * (1 - lam / mu)) := by sorry

end QueueingFundamentals.Bounds
