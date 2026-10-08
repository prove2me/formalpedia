-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_lagrangian_stock_levels_optimal
-- name    : ServiceParts.StockLevels.lagrangian_stock_levels_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:29:14.969097+00:00
-- url     : https://prove2.me/theorems/c1faea29-dfda-4e9f-8647-90c23daf2328
-- title:
--   Section 3.4.2, pp. 58-61 — the Lagrangian stock levels s_i*(θ) solve Problem 4 with budget b = C(θ)
-- statement:
--   Consider $n$ item types managed at a single location by $(s-1, s)$ policies. Item $i$ has stationary compound Poisson demand with steady-state resupply probabilities $p(x \mid \mu_i)$, expected backorders $B_i(s)$, mean lead-time demand $\mu_i = \lambda_i\bar\tau_i\bar u_i$, and unit cost $c_i > 0$. Problem 4 (3.40) with budget $b$ is
--   $$\min \sum_{i=1}^n B_i(s_i) \quad\text{s.t.}\quad \sum_{i=1}^n c_i\,[s_i - \mu_i + B_i(s_i)] \le b, \quad s_i = 0, 1, \dots$$
--
--   Fix a multiplier $\theta > 0$. For every item there is a stock level $s$ with
--   $$\sum_{x \le s} p(x \mid \mu_i) \ge \frac{1}{1 + \theta c_i},$$
--   and if $s_i^*(\theta)$ denotes the smallest one, then the vector $s^*(\theta)$ is an optimal solution of Problem 4 with budget
--   $$b = C(\theta) = \sum_{i=1}^n c_i\,\big[s_i^*(\theta) - \mu_i + B_i(s_i^*(\theta))\big]:$$
--   every vector of nonnegative integer stock levels $s$ with $\sum_i c_i[s_i - \mu_i + B_i(s_i)] \le C(\theta)$ satisfies
--   $$\sum_{i=1}^n B_i(s_i^*(\theta)) \le \sum_{i=1}^n B_i(s_i).$$
--
--   Varying $\theta$ therefore traces optimal backorder–investment trade-offs, which is how the book's bisection algorithm for Problem 4 is justified.
--
--   **Formalization Note** The book's text asserts this by combining Everett's theorem (Theorem 10, p. 57, and the remark on p. 58 that varying $\theta$ yields optimal solutions of Problem 3) with the item-wise criterion of p. 61. $\theta > 0$ and $c_i > 0$ are assumed; at $\theta = 0$ the criterion has no solution. The index set of items is any finite type.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 57-61, Section 3.4.1 Theorem 10 and p. 58, Section 3.4.2, Problem 4 Eq. (3.40), and p. 61 (optimal stock level s* and C(θ))

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem lagrangian_stock_levels_optimal {ι : Type*} [Fintype ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ) (hθ : 0 < θ) :
    (∀ i, (stockSet (d i) (c i) θ).Nonempty) ∧
    ∀ sStar : ι → ℕ, (∀ i, IsLeast (stockSet (d i) (c i) θ) (sStar i)) →
      ∀ s : ι → ℕ, totalInvestment d c s ≤ totalInvestment d c sStar →
        totalBackorders d sStar ≤ totalBackorders d s := by sorry

end ServiceParts.StockLevels
