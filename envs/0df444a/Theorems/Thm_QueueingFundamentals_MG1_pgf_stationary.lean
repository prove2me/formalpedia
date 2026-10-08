-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_pgf_stationary
-- name    : QueueingFundamentals.MG1.pgf_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:38:04.410991+00:00
-- url     : https://prove2.me/theorems/ab492983-fb8f-4e80-acb1-07ff8542126b
-- title:
--   Eq. (5.14) — the generating function of a stationary M/G/1 departure-point distribution
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$, and let $\pi$ be a stationary distribution of the M/G/1 departure-point chain. Write $\Pi(z) = \sum_i \pi_i z^i$ and $K(z) = \sum_i k_i z^i$. Then for every complex $z$ with $|z| \le 1$ and $K(z) \ne z$,
--
--   $$
--   \Pi(z) = \frac{\pi_0 (1-z) K(z)}{K(z) - z}.
--   $$
--
--   No condition on $\rho$ is assumed: the book uses this identity, with $\pi_0$ still unknown, to show that $\rho < 1$ is necessary for a steady state.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.227, Eq. (5.14)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.14), p.227: if `π` is a stationary probability vector of the M/G/1 departure-point
chain (5.10), then its generating function satisfies
`Π(z) = π_0 (1 - z) K(z) / (K(z) - z)` at every `|z| ≤ 1` with `K(z) ≠ z`, where
`K(z) = ∑ k_i z^i`. No condition on `ρ` is assumed (the book uses (5.14) to prove that `ρ < 1`
is necessary, p.235). -/
theorem pgf_stationary (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hK : pgf (arrivalProb lam B) z ≠ z) :
    pgf π z = (π 0 : ℂ) * (1 - z) * pgf (arrivalProb lam B) z /
      (pgf (arrivalProb lam B) z - z) := by sorry

end QueueingFundamentals.MG1
