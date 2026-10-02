-- Prove2me | Theorems.Thm_ServiceParts_Palm_order_count_poisson
-- name    : ServiceParts.Palm.order_count_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:18:09.771562+00:00
-- url     : https://prove2.me/theorems/eb0f8fab-3be0-45c0-8198-58b6d4046ab6
-- title:
--   Eq. (3.5) — the number of orders in [0, t] is Poisson with mean λt
-- statement:
--   In the $(s-1,s)$ backorder system, let $N(t)$ be the number of customer orders placed in $[0,t]$. For every $t > 0$ and every $n \ge 0$,
--   $$P[N(t) = n] = e^{-\lambda t}\frac{(\lambda t)^n}{n!}.$$
--
--   This is the starting point of the proof of Palm's theorem: the orders present at time $t$ are a thinning of these $N(t)$ orders.
--
--   **Formalization Note** The order stream is built from i.i.d. exponential interarrival times with rate $\lambda$, so the statement is the familiar fact that such a renewal process has Poisson marginals.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 39, Eq. (3.5)

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem order_count_poisson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (P {ω | S.orderCount t ω = n}).toReal =
      Real.exp (-(S.rate * t)) * (S.rate * t) ^ n / (Nat.factorial n : ℝ) := by sorry

end ServiceParts.Palm
