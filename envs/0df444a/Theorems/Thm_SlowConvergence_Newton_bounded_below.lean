-- Prove2me | Theorems.Thm_SlowConvergence_Newton_bounded_below
-- name    : SlowConvergence.Newton.bounded_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:01.21598+00:00
-- url     : https://prove2.me/theorems/27652b96-8c32-4b49-8a1f-af0af9425d43
-- title:
--   §3, (3.9)–(3.10), pp. 7–8 — the knot values and the pieces p_k, q_k are nonnegative, so $f_2$ is bounded below by zero
-- statement:
--   Let $0 < \tau < 1$ and $\eta = \tau/(4-2\tau)$. Define the knot values of the two coordinate functions by (3.9) and (3.10):
--   $$f_{2,1}([x_0]_1) = \tfrac12\zeta(1+2\eta),\qquad f_{2,1}([x_{k+1}]_1) = f_{2,1}([x_k]_1) - \tfrac12\Big(\frac1{k+1}\Big)^{1+2\eta},$$
--   $$f_{2,2}([x_0]_2) = \tfrac12\zeta(2),\qquad f_{2,2}([x_{k+1}]_2) = f_{2,2}([x_k]_2) - \tfrac12\Big(\frac1{k+1}\Big)^{2}.$$
--   Then for every $k \ge 0$:
--
--   1. $f_{2,1}([x_k]_1) \ge 0$ and $f_{2,2}([x_k]_2) \ge 0$;
--   2. $f_k = f_{2,1}([x_k]_1) + f_{2,2}([x_k]_2)$, where $f_k$ is the prescribed value (3.3);
--   3. consequently $f_k \ge 0$;
--   4. the Hermite pieces are nonnegative on their intervals: $p_k(t) \ge 0$ for $t \in [0,\mu_k]$ and $q_k(t) \ge 0$ for $t \in [0,1]$, where $p_k$ is the quintic (2.11) with coefficients (2.14) at $\alpha_k = 1$ and $q_k$ the quintic of pp. 7–8.
--
--   Since $f_2([x]_1,[x]_2) = p_k([x]_1 - [x_k]_1) + f_{2,1}([x_{k+1}]_1) + q_j([x]_2 - j) + f_{2,2}([x_{j+1}]_2)$ on the cell $[[x_k]_1,[x_{k+1}]_1] \times [j, j+1]$, items 1 and 4 give $f_2 \ge 0$ on the whole nonnegative quadrant where the page builds $f_2$.
--
--   Each knot value is a tail of a convergent zeta series, which is why the decreasing sequence of function values stays above zero; this is the step "$f_2$ is bounded below by zero" of the example.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 7, §3, (3.9)–(3.10); p. 8, §3; (3.3), p. 6

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §3, (3.9)–(3.10), p. 7 and p. 8: "The fact that f_2 is
bounded below by zero results from (3.10) and the fact that ζ(2) = π²/6." For `0 < τ < 1` and every
`k ≥ 0`, the knot values `f_{2,1}([x_k]_1)` of (3.9) and `f_{2,2}([x_k]_2)` of (3.10) are nonnegative,
they add up to the prescribed value `f_k` of (3.3), and hence `f_k ≥ 0`. Moreover the pieces are
nonnegative on their intervals, `p_k ≥ 0` on `[0, µ_k]` and `q_k ≥ 0` on `[0, 1]`, so that
`f_2([x]_1, [x]_2) = p_k([x]_1 − [x_k]_1) + f_{2,1}([x_{k+1}]_1) + q_j([x]_2 − j) + f_{2,2}(j + 1) ≥ 0`
everywhere on the nonnegative quadrant where the page builds `f_2`. -/
theorem bounded_below (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 ≤ f21knot τ k ∧ 0 ≤ f22knot k ∧ fk τ k = f21knot τ k + f22knot k ∧ 0 ≤ fk τ k ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (mu τ k), 0 ≤ p τ k t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q k t) := by sorry

end SlowConvergence.Newton
