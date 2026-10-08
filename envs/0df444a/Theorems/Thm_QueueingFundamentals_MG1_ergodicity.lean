-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_ergodicity
-- name    : QueueingFundamentals.MG1.ergodicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:38:21.885022+00:00
-- url     : https://prove2.me/theorems/b847d372-b9e9-491f-9702-32d434ac2902
-- title:
--   §5.1.4 — the M/G/1 departure-point chain has a steady state if and only if ρ < 1
-- statement:
--   Let $\lambda > 0$ and let $B$ be a service-time distribution on $[0,\infty)$ with finite mean $\mathrm E[S]$; put $\rho = \lambda\,\mathrm E[S]$. The M/G/1 departure-point chain has exactly one stationary distribution if and only if
--
--   $$
--   \rho < 1 .
--   $$
--
--   If $\rho \ge 1$ it has none.
--
--   This is the ergodicity condition of the M/G/1 queue: the stationary quantities of §5.1 exist exactly when the server is not overloaded.
--
--   **Formalization Note** The book concludes that the chain "possesses identical stationary and long-run distributions when $\rho < 1$" and that "$\rho < 1$ is necessary and sufficient for steady state". The statement records the stationary-distribution part, as existence and uniqueness (`∃!`); convergence of the chain's long-run distribution is not stated.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.233–235, §5.1.4 Ergodic Theory

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- §5.1.4, pp.233–235: for Poisson(`λ`) arrivals and a service distribution `B` on `[0, ∞)`
with finite mean `E[S]`, the M/G/1 departure-point chain (5.10) has a stationary distribution,
and then exactly one, if and only if `ρ = λ E[S] < 1`. -/
theorem ergodicity (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) :
    (∃! π : ℕ → ℝ, IsStationaryDist (transitionMatrix lam B) π) ↔ utilization lam B < 1 := by sorry

end QueueingFundamentals.MG1
