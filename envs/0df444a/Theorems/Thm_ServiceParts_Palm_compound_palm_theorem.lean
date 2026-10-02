-- Prove2me | Theorems.Thm_ServiceParts_Palm_compound_palm_theorem
-- name    : ServiceParts.Palm.compound_palm_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:39:59.59+00:00
-- url     : https://prove2.me/theorems/a1bccf21-eabb-4ab0-98b6-669a5fabcc98
-- title:
--   Theorem 7 — compound Poisson demand: units in resupply are compound Poisson with parameter λτ̄
-- statement:
--   Consider the $(s-1,s)$ backorder system with compound Poisson demand: customer orders arrive as a Poisson process with rate $\lambda > 0$, the $k$-th order asks for $X_k \ge 1$ units with i.i.d. sizes $P[X_k = j] = u_j$, and all units of one order share one resupply time, drawn from a common distribution with density $g$, distribution function $G$ and finite mean $\bar\tau$. Interarrival times, resupply times and order sizes are mutually independent, and the system is empty at time $0$. Let $Y(t)$ be the number of units in resupply at time $t$. Then for every $n \ge 0$
--   $$\lim_{t\to\infty} P[Y(t) = n] = \sum_{j=0}^{n} u^{(j)}_n\, e^{-\lambda\bar\tau}\frac{(\lambda\bar\tau)^j}{j!},$$
--   where $u^{(j)}_n$ is the probability that $j$ customers ask for $n$ units in total. In the book's form: $P[X = n] = \sum_{j\ge1} u^{(j)}_n e^{-\lambda\bar\tau}(\lambda\bar\tau)^j/j!$ for $n \ge 1$ and $P[X = 0] = e^{-\lambda\bar\tau}$, the compound Poisson distribution with mean $\lambda\bar\tau\bar u$, $\bar u$ the mean order size.
--
--   With $u_1 = 1$ this is Palm's theorem.
--
--   **Formalization Note** "Steady state probability" is pinned, as for Theorem 6, to $\lim_{t\to\infty}P[Y(t) = n]$ for the system empty at time $0$. The distribution is identified through the pmf (3.22)–(3.23); the mean $\lambda\bar\tau\bar u$ is the mean of that law (possibly $+\infty$ when $\bar u = \infty$) and is not stated separately.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 43-44, Theorem 7 (proof p. 44, Eqs. (3.22)-(3.23))

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem compound_palm_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF (S.rate * S.meanResupply) S.sizePMF n)) := by sorry

end ServiceParts.Palm
