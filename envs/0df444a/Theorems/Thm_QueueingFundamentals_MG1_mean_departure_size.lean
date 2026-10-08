-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_mean_departure_size
-- name    : QueueingFundamentals.MG1.mean_departure_size
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:38:30.84876+00:00
-- url     : https://prove2.me/theorems/94d66fd3-9897-42c1-ae72-d6ed9c4b3d94
-- title:
--   Eq. (5.7) — the Pollaczek–Khintchine mean system size at departure points
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$ with finite second moment and variance $\sigma_B^2$, let $\rho = \lambda\,\mathrm E[S] < 1$, and let $\pi$ be the stationary distribution of the M/G/1 departure-point chain. Then the mean number left behind by a departure is finite and equals
--
--   $$
--   L^{(D)} = \sum_{n=0}^{\infty} n\,\pi_n = \rho + \frac{\rho^2 + \lambda^2\sigma_B^2}{2(1-\rho)} .
--   $$
--
--   This is the Pollaczek–Khintchine mean-value formula in departure-point form; with $W_q = L_q/\lambda$ and the equality of departure-point and time-average probabilities it is equivalent to (5.2).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.225, Eq. (5.7)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.7), p.225: with `ρ = λ E[S] < 1` and a service distribution with finite second
moment and variance `σ_B²`, the stationary departure-point system size has finite mean
`L^{(D)} = ∑ n π_n = ρ + (ρ² + λ² σ_B²) / (2(1 - ρ))`. -/
theorem mean_departure_size (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hint2 : Integrable (fun t : ℝ => t ^ 2) B)
    (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π) :
    HasSum (fun n : ℕ => (n : ℝ) * π n)
      (utilization lam B + (utilization lam B ^ 2 + lam ^ 2 * serviceVariance B) /
        (2 * (1 - utilization lam B))) := by sorry

end QueueingFundamentals.MG1
