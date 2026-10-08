-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_theta_max_zero_stock
-- name    : ServiceParts.StockLevels.theta_max_zero_stock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:28:45.818958+00:00
-- url     : https://prove2.me/theorems/52ee5603-9d79-4c86-9b23-a51ec7dc53eb
-- title:
--   Section 3.4.2, p. 63 — θ_max = max_i (1/c_i)(1/p(0|µ_i) − 1) makes every s_i*(θ_max) = 0
-- statement:
--   Consider $n \ge 1$ item types with compound Poisson demand and unit costs $c_i > 0$, and let $p(0 \mid \mu_i)$ be the probability that no unit of item $i$ is in resupply. For each $i$ put
--   $$\theta_i = \frac{1}{c_i}\Big(\frac{1}{p(0 \mid \mu_i)} - 1\Big).$$
--   Then $\theta_i > 0$ and $p(0 \mid \mu_i) = 1/(1 + \theta_i c_i)$. Moreover, with $\theta_{\max} = \max_i \theta_i$, the smallest stock level $s$ with
--   $$\sum_{x \le s} p(x \mid \mu_i) \ge \frac{1}{1 + \theta_{\max} c_i}$$
--   is $s = 0$ for every item $i$, that is, $s_i^*(\theta_{\max}) = 0$.
--
--   This gives the upper end of the bisection interval $[\theta_{\min}, \theta_{\max}]$ used by the book's algorithm for Problem 4.
--
--   **Formalization Note** The item index set is finite and nonempty, so that the maximum exists.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 63, Section 3.4.2 (θ with p(0|µ_i) = 1/(1 + θc_i), θmax)

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem theta_max_zero_stock {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ i, 0 < thetaZero (d i) (c i) ∧
      (d i).pmf 0 = 1 / (1 + thetaZero (d i) (c i) * c i)) ∧
    ∀ i, IsLeast
      (stockSet (d i) (c i) (Finset.univ.sup' Finset.univ_nonempty
        (fun j => thetaZero (d j) (c j)))) 0 := by sorry

end ServiceParts.StockLevels
