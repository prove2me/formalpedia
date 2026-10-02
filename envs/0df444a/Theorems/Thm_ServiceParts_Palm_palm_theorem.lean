-- Prove2me | Theorems.Thm_ServiceParts_Palm_palm_theorem
-- name    : ServiceParts.Palm.palm_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:36:57.005305+00:00
-- url     : https://prove2.me/theorems/286117d8-3d1c-463e-84f9-c88f28c58974
-- title:
--   Theorem 6 — Palm's theorem: units in resupply are Poisson with mean λτ̄ in steady state
-- statement:
--   Consider an item managed with an $(s-1,s)$ policy with backorders. Customer orders, each for one unit, arrive as a Poisson process with rate $\lambda > 0$, starting from an empty system at time $0$. Each order immediately triggers a resupply order. The resupply times are independent and identically distributed from order to order, independent of the arrival process, nonnegative, with density $g$, distribution function $G$ and finite mean $\bar\tau$. Let $X(t)$ be the number of units in resupply at time $t$. Then for every $x \ge 0$ the steady-state probability that $x$ units are in resupply is
--   $$\lim_{t\to\infty} P[X(t) = x] = e^{-\lambda\bar\tau}\,\frac{(\lambda\bar\tau)^x}{x!}. \tag{3.4}$$
--
--   The limiting law depends on the resupply-time distribution only through its mean $\bar\tau$. It is the basis of every stock-level computation for $(s-1,s)$ systems: on-hand inventory and backorders at stock level $s$ are $(s - X)^+$ and $(X - s)^+$.
--
--   **Formalization Note** The book writes "steady state probability"; its proof computes $P[X(t) = x]$ for the system empty at time $0$ and lets $t \to \infty$ ((3.8)–(3.11)), so the statement is that limit. The stock level $s$ named in the book does not enter: in the backorder case $X(t)$ does not depend on it. Independence of resupply times from arrivals is a standing assumption of the model, used on p. 40.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 39, Theorem 6 (Eq. (3.4); proof pp. 39-41, Eqs. (3.5)-(3.11))

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem palm_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (x : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = x}).toReal) atTop
      (𝓝 (Real.exp (-(S.rate * S.meanResupply)) * (S.rate * S.meanResupply) ^ x /
        (Nat.factorial x : ℝ))) := by sorry

end ServiceParts.Palm
