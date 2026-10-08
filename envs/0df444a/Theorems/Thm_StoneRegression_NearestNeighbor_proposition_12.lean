-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_proposition_12
-- name    : StoneRegression.NearestNeighbor.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:17.841527+00:00
-- url     : https://prove2.me/theorems/8563ade7-7043-4ebf-a866-e92bc31d5ed2
-- title:
--   Proposition 12, p. 613 — the swapped nearest neighbor weights satisfy Σᵢ Uₙᵢ(X) ≤ β(d, a/b)
-- statement:
--   Fix $n \ge 1$, a coefficient row $c_{n1} \ge \dots \ge c_{nn} \ge 0$ with $\sum_i c_{ni} = 1$, and nonnegative scales $s_n$ satisfying condition (7) with constants $0 < a \le b$. Let $W_n$ be the nearest neighbor probability weight function (8), and let
--   $$U_{ni}(X) = W_{ni}(X_i, X_1, \dots, X, \dots, X_n)$$
--   be the weight of slot $i$ when $X_i$ is the query point and $X$ takes its place in the sample. Then for all points $X, X_1, \dots, X_n \in \mathbb R^d$,
--   $$\sum_{i=1}^n U_{ni}(X) \le \beta(d, a/b),$$
--   where $\beta(d,c)$ is the least number of sets in $\mathcal V(d,c)$ covering $\mathbb R^d$.
--
--   The bound says that a single point $X$ cannot carry much total weight as a neighbor of the other sample points, uniformly in $n$ and in the configuration. Through the exchangeability of the sample it yields condition (1) for nearest neighbor weights (Proposition 11).
--
--   **Formalization Note** The statement is deterministic: the points are fixed, and only nonnegativity of the scales and (7) (read for all points) are assumed, which are the only properties the page's proof uses. The swap acts on both the weights and the scales: the query is $X_i$ and the sample is $X_1, \dots, X_n$ with $X$ in slot $i$. $\beta$ is an infimum over $\mathbb N$, and the existence of a finite cover is not assumed.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 12 and the definition of U_ni, p. 613; proof pp. 613–615

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_12 {d : ℕ} (s : ScaleSeq d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hs0 : ∀ n x xs j, 0 ≤ s n x xs j) (h7 : Cond7 s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∑ i, swapW (nnWeights c s) n x xs i) ≤ (beta d (a / b) : ℝ) := by sorry

end StoneRegression.NearestNeighbor
