-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_values_bounded_below
-- name    : SlowConvergence.SteepestDescent.values_bounded_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:11.033465+00:00
-- url     : https://prove2.me/theorems/e5318002-949c-4fca-b590-26ac0854701f
-- title:
--   §2, p. 5 — $f_k - f_{k+1} \le \frac12(1/(k+1))^{1+2\eta}$, hence $f_k \ge 0$ for all $k$
-- statement:
--   Let $0 < \tau < 1$, $\eta = \tau/(4-2\tau)$, and let the step lengths satisfy (2.6): $0 < \underline\alpha \le \alpha_k \le \overline\alpha < 2$ for all $k$. Let $f_0 = \tfrac12\zeta(1+2\eta)$ and $f_{k+1} = f_k - \alpha_k(1-\tfrac12\alpha_k)(1/(k+1))^{1+2\eta}$ be the prescribed values (2.8). Then for every $k \ge 0$
--   $$f_k - f_{k+1} = \alpha_k\big(1-\tfrac12\alpha_k\big)\Big(\frac{1}{k+1}\Big)^{1+2\eta} \le \frac12\Big(\frac{1}{k+1}\Big)^{1+2\eta},$$
--   and consequently, by the definition of $\zeta(1+2\eta) = \sum_{n\ge1} n^{-(1+2\eta)}$,
--   $$f_k \ge 0 \qquad \text{for all } k \ge 0.$$
--   This is the bound from which the paper concludes that the objective $f_1$ of the example is bounded below.
--
--   **Formalization Note** The statement is made about the prescribed values $f_k = f_1(x_k)$ at the iterates; a lower bound for $f_1$ between the iterates is part of the main theorem.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 5, §2, display after (2.17)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, p. 5: under (2.6),
`f_k − f_{k+1} = α_k(1 − ½α_k)(1/(k+1))^{1+2η} ≤ ½(1/(k+1))^{1+2η}`, and together with
`f_0 = ½ζ(1 + 2η)` this keeps every prescribed value nonnegative: `f_k ≥ 0` for all `k ≥ 0`. -/
theorem values_bounded_below (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) :
    (∀ k : ℕ, fk τ α k - fk τ α (k + 1) ≤ 1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ)) ∧
      ∀ k : ℕ, 0 ≤ fk τ α k := by sorry

end SlowConvergence.SteepestDescent
