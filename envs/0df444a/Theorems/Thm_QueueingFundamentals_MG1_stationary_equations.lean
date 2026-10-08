-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_stationary_equations
-- name    : QueueingFundamentals.MG1.stationary_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:38:00.321078+00:00
-- url     : https://prove2.me/theorems/cf619ccd-b8b6-4f67-b67b-9d1ad2fdda10
-- title:
--   Eq. (5.12) — the stationary equations of the M/G/1 departure-point chain
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$, let $k_i$ be the probability of $i$ arrivals during a service time, and let $P$ be the transition matrix of the M/G/1 departure-point chain. A probability vector $\pi$ on $\{0,1,2,\dots\}$ satisfies $\pi P = \pi$ if and only if
--
--   $$
--   \pi_i = \pi_0 k_i + \sum_{j=1}^{i+1} \pi_j k_{i-j+1} \qquad (i = 0,1,2,\dots).
--   $$
--
--   This is the form of the stationary equations from which the generating function $\Pi(z)$ is obtained.
--
--   **Formalization Note** The index $i-j+1$ is written `i + 1 - j`, which is exact in `ℕ` for $j \le i+1$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.227, Eq. (5.12)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.12), p.227: a probability vector `π` on `ℕ` satisfies `πP = π` for the M/G/1
departure-point matrix (5.10) iff
`π_i = π_0 k_i + ∑_{j=1}^{i+1} π_j k_{i-j+1}` for every `i ≥ 0`. -/
theorem stationary_equations (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (π : ℕ → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ1 : HasSum π 1) :
    IsStationaryDist (transitionMatrix lam B) π ↔
      ∀ i : ℕ, π i = π 0 * arrivalProb lam B i +
        ∑ j ∈ Finset.Icc 1 (i + 1), π j * arrivalProb lam B (i + 1 - j) := by sorry

end QueueingFundamentals.MG1
