-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_cross_sum_upper_bound
-- name    : RandomListsMatching.GeneralRates.cross_sum_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:41.578202+00:00
-- url     : https://prove2.me/theorems/d65b1377-4dfe-4a77-bd42-ea197a88da79
-- title:
--   §5.4, p. 15 display — Σ g(f_{a₁}, m_{a₁,a}) ≤ e⁻¹(s_a − β_a) + g(1, β_a), from (5)
-- statement:
--   Let $g$ be the function of Claim 2 (with $h$ as there). Let $x_1, \dots, x_k$ and $y_1, \dots, y_k$ be reals with $0 \le x_j \le y_j \le 1$ for every $j$, and let $j_0$ be any index. Then
--   $$
--   \sum_{j=1}^k g(y_j, x_j) \;\le\; e^{-1}\Bigl(\sum_{j=1}^k x_j - x_{j_0}\Bigr) + g(1, x_{j_0}).
--   $$
--
--   This is the display of p. 15 of Jaillet and Lu, "from inequality (5)", with $x_j = m_{a_1,a}$, $y_j = f_{a_1}$ and $j_0 = a_1^*$, so that $x_{j_0} = \beta_a$ and $\sum_j x_j = s_a$: every term but the singled-out one is bounded by (5), and the singled-out one by the monotonicity of $g$ in its first argument.
--
--   **Formalization Note** On the page $j_0 = a_1^*$ is the index attaining $\beta_a = \max_{a_1} m_{a,a_1}$; the inequality holds for every index and its argument does not use maximality, so the statement is made for any $j_0$ (a disclosed generalization). The page's singled-out term $g(f_{a_1}, \beta_a)$ means $g(f_{a_1^*}, \beta_a)$. The hypotheses $x_j \le y_j \le 1$ are the paper's $m_{a_1,a} \le s_{a_1} \le f_{a_1} \le 1$ (with $f_{a_d} = 1$ for the dummy).
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, display after "On the other hand, from inequality (5)"

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem cross_sum_upper_bound {k : ℕ} (x y : Fin k → ℝ) (j₀ : Fin k)
    (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1) :
    ∑ j, g (y j) (x j) ≤ Real.exp (-1) * (∑ j, x j - x j₀) + g 1 (x j₀) := by sorry

end RandomListsMatching.GeneralRates
