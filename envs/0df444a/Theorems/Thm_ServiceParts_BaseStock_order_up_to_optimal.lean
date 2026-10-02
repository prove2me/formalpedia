-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_order_up_to_optimal
-- name    : ServiceParts.BaseStock.order_up_to_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:35:29.82417+00:00
-- url     : https://prove2.me/theorems/da8af656-d153-4992-8c8f-810a3607487b
-- title:
--   Theorem 2 — optimality of order-up-to policies in the n-period Karlin–Scarf recursion
-- statement:
--   In the model of Section 2.1 with lead time one period, consider the $n$-period recursion
--   $$
--   f_1(y) = L(y), \qquad f_n(y) = \min_{u \ge 0}\Big\{ c\,u + L(y) + \alpha\int_0^\infty f_{n-1}(y+u-x)\,g(x)\,dx \Big\}.
--   $$
--   Then:
--
--   1. for every horizon $n \ge 2$ an order-up-to policy is optimal: either there is a real level $s_n^*$ such that
--   $$
--   u_n^*(y) = \max\{0,\ s_n^* - y\}
--   $$
--   attains the minimum for every inventory position $y$, or ordering nothing attains the minimum for every $y$ (the level $s_n^* = -\infty$);
--   2. there is $N \ge 2$ such that for every $n \ge N$ the level $s_n^*$ is a real number.
--
--   This is Theorem 2 of the book in the form its proof establishes: an induction over a finite horizon $n$ with lead time $\tau = 1$.
--
--   **Formalization Note** The book states Theorem 2 for "the optimal policy" with lead time $\tau$ and a real level $s^*$, but proves it for the finite-horizon recursion with $\tau = 1$; the passage $n \to \infty$ is left as an unproved conjecture on p. 21. The book also claims a real level for every $n \ge 2$, starting from a base case "left to the reader". Under its assumption $b > \frac{1-\alpha}{\alpha}c$ that base case fails when $c > \alpha b$ (e.g. $\alpha = \tfrac12$, $c = 1$, $b = \tfrac32$): the two-period problem then never orders. The statement is therefore corrected to allow the level $-\infty$, and part 2 records the finiteness that the assumption does guarantee for all long enough horizons. Optimality is against all orders $u \ge 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 18, Theorem 2 (n-period form of the proof, pp. 18-21, eq. (2.5))

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Theorem 2, p. 18, in the n-period form of its proof (lead time τ = 1), corrected at the
base case: (i) for every horizon n ≥ 2 an order-up-to rule is optimal at every inventory
position — either with a real level s, u*(y) = max{0, s − y}, or with level −∞ (never order);
(ii) there is N ≥ 2 such that for every n ≥ N the level can be taken real. -/
theorem order_up_to_optimal (M : Model) :
    (∀ n : ℕ, 2 ≤ n →
        (∃ s : ℝ, M.IsOrderUpToOptimal n s) ∨ (∀ y : ℝ, M.IsOptimalOrder n y 0)) ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ s : ℝ, M.IsOrderUpToOptimal n s := by sorry

end ServiceParts.BaseStock
