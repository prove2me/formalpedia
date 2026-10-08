-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_pk_transform
-- name    : QueueingFundamentals.MG1.pk_transform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:38:42.205423+00:00
-- url     : https://prove2.me/theorems/89789e20-fe63-499f-955d-5a77713cb484
-- title:
--   Eqs. (5.15)–(5.16) — the Pollaczek–Khintchine transform formula for the M/G/1 queue
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$ with finite mean $\mathrm E[S]$, and assume
--
--   $$
--   \rho = \lambda\,\mathrm E[S] < 1 .
--   $$
--
--   Let $k_i$ be the probability of $i$ Poisson arrivals during a service time and $K(z) = \sum_i k_i z^i$. Then:
--
--   1. the M/G/1 departure-point chain has a stationary distribution;
--   2. every stationary distribution $\pi$ has $\pi_0 = 1 - \rho$ (5.15);
--   3. for every complex $z$ with $|z| \le 1$ and $z \ne 1$, $K(z) \ne z$ and
--
--   $$
--   \Pi(z) = \sum_{i=0}^\infty \pi_i z^i = \frac{(1-\rho)(1-z)K(z)}{K(z) - z} .
--   $$
--
--   At $z = 1$ the right side is $0/0$ and $\Pi(1) = 1$. This transform formula determines the whole stationary departure-point distribution from the service distribution; its derivatives at $z = 1$ give the moments of the system size.
--
--   **Formalization Note** The book's "the steady-state probabilities are given by (5.16)" is stated in both halves: a stationary probability vector exists, and every one satisfies (5.15)–(5.16). The point $z = 1$ is excluded; the non-vanishing of $K(z) - z$ elsewhere in the closed disk is part of the conclusion.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.227, Eqs. (5.15)–(5.16)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eqs. (5.15)–(5.16), p.227, the Pollaczek–Khintchine transform formula. Let `λ > 0`, let the
service distribution `B` be a probability measure on `[0, ∞)` with finite mean `E[S]`, and
let `ρ = λ E[S] < 1`. Then the M/G/1 departure-point chain (5.10) has a stationary probability
vector, and every stationary probability vector `π` has `π_0 = 1 - ρ` and, for every
`|z| ≤ 1` with `z ≠ 1`, `K(z) ≠ z` and
`Π(z) = (1 - ρ)(1 - z) K(z) / (K(z) - z)`. At `z = 1` the right side is `0/0`; there
`Π(1) = 1`, which is part of `IsStationaryDist`. -/
theorem pk_transform (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1) :
    (∃ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ∧
      ∀ π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π →
        π 0 = 1 - utilization lam B ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          pgf (arrivalProb lam B) z ≠ z ∧
          pgf π z = (1 - (utilization lam B : ℂ)) * (1 - z) * pgf (arrivalProb lam B) z /
            (pgf (arrivalProb lam B) z - z) := by sorry

end QueueingFundamentals.MG1
