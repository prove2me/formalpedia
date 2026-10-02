-- Prove2me | Theorems.Thm_ServiceParts_Palm_delayed_due_dates
-- name    : ServiceParts.Palm.delayed_due_dates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:45:50.543261+00:00
-- url     : https://prove2.me/theorems/ef2fc3ae-8460-4a44-8755-ecd382cd1cd9
-- title:
--   Theorem 9 — delayed due dates: units in resupply for at least T are compound Poisson with parameter λτ̄α
-- statement:
--   Consider the compound Poisson $(s-1,s)$ backorder system of Theorem 7 (Poisson orders with rate $\lambda > 0$, i.i.d. order sizes with law $u$, one common resupply time per order with density $g$, distribution function $G(t) = \int_0^t g(\tau)\,d\tau$ and finite mean $\bar\tau$, all mutually independent, empty at time $0$). Fix a due-date delay $T \ge 0$ and let $Y_T(t)$ be the number of units in resupply at time $t$ each of which has been in the resupply system for at least $T$ time units. Put
--   $$\alpha = \frac1{\bar\tau}\int_T^\infty [1 - G(t)]\,dt. \tag{3.35}$$
--   Then for every $n \ge 0$
--   $$\lim_{t\to\infty} P[Y_T(t) = n] = p(n \mid \lambda\bar\tau\alpha) = \sum_{y=0}^{n}\frac{(\lambda\bar\tau\alpha)^y e^{-\lambda\bar\tau\alpha}}{y!}\,u^{(y)}_n,$$
--   where $u^{(y)}_n$ is the probability that $y$ customers generate a total demand of $n$ units.
--
--   For $T = 0$, $\alpha = 1$ and this is Theorem 7. When each demand must be met within $T$ time units of its arrival rather than immediately, $Y_T$ counts the units whose demand is due, which is what the stock level has to cover.
--
--   **Formalization Note** "Steady state probability" is pinned to $\lim_{t\to\infty}$ for the system empty at time $0$. An order placed at $T_k$ counts when $T_k + T \le t < T_k + L_k$. The mean resupply time is positive (the resupply time has a density), so $\alpha$ is well defined.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 46-47, Theorem 9 (Eqs. (3.35)-(3.36))

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem delayed_due_dates {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.agedUnitsInResupply T t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF
        (S.rate * S.meanResupply *
          ((1 / S.meanResupply) * ∫ u in Set.Ioi T, (1 - S.resupplyCdf u)))
        S.sizePMF n)) := by sorry

end ServiceParts.Palm
