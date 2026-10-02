-- Prove2me | Theorems.Thm_ServiceParts_Palm_units_in_resupply_poisson_finite_time
-- name    : ServiceParts.Palm.units_in_resupply_poisson_finite_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:32:28.085467+00:00
-- url     : https://prove2.me/theorems/a520679d-c5a0-4d2e-a4ed-7bb807f64ffe
-- title:
--   Eq. (3.8) — at every t > 0 the units in resupply are Poisson with mean λ∫₀ᵗ[1 − G(u)]du
-- statement:
--   In the $(s-1,s)$ backorder system, started empty at time $0$, let $X(t)$ be the number of units in resupply at time $t$ and $G$ the resupply-time distribution function. For every $t > 0$ and every $x \ge 0$,
--   $$q_t(x) = P[X(t) = x] = e^{-\lambda\int_0^t [1-G(u)]\,du}\,\frac{\big[\lambda\int_0^t [1-G(u)]\,du\big]^x}{x!}.$$
--
--   This is the finite-time law from which Palm's theorem follows by letting $t \to \infty$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 40-41, Eq. (3.8)

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem units_in_resupply_poisson_finite_time {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-(S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) *
        (S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x / (Nat.factorial x : ℝ) := by sorry

end ServiceParts.Palm
