-- Prove2me | Theorems.Thm_ServiceParts_Palm_units_binomial_given_orders
-- name    : ServiceParts.Palm.units_binomial_given_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:27:51.22374+00:00
-- url     : https://prove2.me/theorems/0a33d0ab-a685-447d-a86d-da6c57c46efe
-- title:
--   Eq. (3.7) — given N(t) = n, the units in resupply at t are Binomial(n, p)
-- statement:
--   In the $(s-1,s)$ backorder system with resupply-time distribution function $G$, fix $t > 0$ and let
--   $$p = \frac1t\int_0^t [1 - G(u)]\,du$$
--   be the probability that an order placed at a uniformly distributed time in $[0,t]$ is still in resupply at time $t$. Let $X(t)$ be the number of units in resupply at time $t$ and $N(t)$ the number of orders placed in $[0,t]$. Then for all $n, x \ge 0$,
--   $$q_t(x \mid n) = P[X(t) = x \mid N(t) = n] = \binom{n}{x} p^x (1-p)^{n-x}.$$
--
--   This binomial thinning, averaged over the Poisson law of $N(t)$, yields the Poisson law of $X(t)$ at every finite time.
--
--   **Formalization Note** The conditional probability is written as $P[X(t) = x,\ N(t) = n] = P[N(t) = n]\binom{n}{x}p^x(1-p)^{n-x}$. For $x > n$ the binomial coefficient is $0$ (and so is the left side).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 40, Eq. (3.7) with the display for p above it

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem units_binomial_given_orders {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n x : ℕ) :
    (P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n})).toReal =
      (P {ω | S.orderCount t ω = n}).toReal *
        ((Nat.choose n x : ℝ) * ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
          (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x)) := by sorry

end ServiceParts.Palm
