-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_goldstein_armijo
-- name    : SlowConvergence.SteepestDescent.goldstein_armijo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:20.664146+00:00
-- url     : https://prove2.me/theorems/2b8b0525-b1cf-449b-add3-db882a8c2e0d
-- title:
--   §2, p. 4 — the step lengths result from a Goldstein–Armijo linesearch (interval corrected)
-- statement:
--   Let $0 < \tau < 1$ and consider the prescribed steps $s_k$, values $f_k$ and gradients $g_k$ of (2.5)–(2.9). Let $a, b$ be constants with $0 < a < b < 1$ (the paper's $\alpha < \beta$). If the step length satisfies
--   $$2(1-b) \le \alpha_k \le 2(1-a),$$
--   then $-s_k g_k = \alpha_k |g_k|^2$, and the step satisfies both Goldstein–Armijo conditions
--   $$f_k - f_{k+1} \ge -a\, s_k g_k = a\,\alpha_k |g_k|^2 \qquad\text{and}\qquad f_k - f_{k+1} \le -b\, s_k g_k = b\,\alpha_k |g_k|^2.$$
--   So the steps of the example are those of a steepest descent method with a Goldstein–Armijo linesearch.
--
--   **Formalization Note** The page writes the interval as $2(1-\alpha) < \alpha_k < 2(1-\beta)$, which is empty when $\alpha < \beta$. By (2.8), $f_k - f_{k+1} = (1-\tfrac12\alpha_k)\,\alpha_k|g_k|^2$, so the two conditions hold exactly when $2(1-\beta) \le \alpha_k \le 2(1-\alpha)$; that corrected interval is stated. The linesearch constants are named $a, b$ to keep them apart from the step lengths $\alpha_k$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, first paragraph

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, p. 4 (Goldstein–Armijo remark), corrected:
for constants `0 < a < b < 1` (the paper's `α < β`), if `2(1 − b) ≤ α_k ≤ 2(1 − a)` then the step of
(2.5)–(2.9) satisfies both Goldstein–Armijo conditions
`f_k − f_{k+1} ≥ −a s_k g_k = a α_k |g_k|²` and `f_k − f_{k+1} ≤ −b s_k g_k = b α_k |g_k|²`.

Formalization Note: the page prints the interval as `2(1 − α) < α_k < 2(1 − β)`, which is empty for
`α < β`; the two conditions hold exactly when `2(1 − β) ≤ α_k ≤ 2(1 − α)`, and that interval is stated. -/
theorem goldstein_armijo (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (α : ℕ → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℕ)
    (hαk : 2 * (1 - b) ≤ α k ∧ α k ≤ 2 * (1 - a)) :
    -(sk τ α k * gk τ k) = α k * |gk τ k| ^ 2 ∧
      -(a * (sk τ α k * gk τ k)) ≤ fk τ α k - fk τ α (k + 1) ∧
      fk τ α k - fk τ α (k + 1) ≤ -(b * (sk τ α k * gk τ k)) := by sorry

end SlowConvergence.SteepestDescent
