-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_second_deriv_bound
-- name    : SlowConvergence.SteepestDescent.second_deriv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:29.629035+00:00
-- url     : https://prove2.me/theorems/6e3c75f7-c1ad-4a51-abe8-6e9e59c40f87
-- title:
--   §2 (2.17), p. 5 — $|p_k''(t)| \le 1 + 150|\phi_k| \le 1 + 150\max[1,\overline\alpha]/\underline\alpha$ on $[0,\mu_k]$
-- statement:
--   Let $0 < \tau < 1$ and let the step lengths satisfy (2.6): $0 < \underline\alpha \le \alpha_k \le \overline\alpha < 2$ for all $k$. Let $p_k$ be the quintic Hermite piece (2.11), (2.14) on $[0,\mu_k]$ and $\phi_k$ as in (2.15). Then for all $k \ge 0$ and all $t \in [0, \mu_k]$,
--   $$|p_k''(t)| \le 1 + 150\,|\phi_k| \qquad\text{and}\qquad |p_k''(t)| \le 1 + 150\,\frac{\max[1,\overline\alpha]}{\underline\alpha}.$$
--   The second bound is uniform in $k$, so the second derivative of the glued function $f_1$ is bounded and its gradient is Lipschitz continuous, as AS.0 requires.
--
--   **Formalization Note** Only the two end bounds of the printed chain (2.17) are stated. Its middle line, $2|c_{2,k}| + 6|c_{3,k}|\mu_k + 12|c_{4,k}|\mu_k^2 + 20|c_{5,k}|\mu_k^3$, equals $1 + 168|\phi_k|$ and is not bounded by $1 + 150|\phi_k|$; and the inequality $|\phi_k| \le 1$ cited after (2.17) fails for small $\alpha_k$. Both end bounds are nevertheless true: on $[0,\mu_k]$ one has $|p_k''(t) - 1| \le 3.94\,|\phi_k|$, and $|\phi_k| < \max[1,\overline\alpha]/\underline\alpha$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 5, §2, (2.17)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, (2.17), p. 5: under (2.6), for all `k ≥ 0` and
all `t ∈ [0, µ_k]`, `|p_k''(t)| ≤ 1 + 150|φ_k| ≤ 1 + 150 max[1, ᾱ]/α̲`.

Formalization Note: only the end bounds of the printed chain are stated. The middle line
`2|c_{2,k}| + 6|c_{3,k}|µ_k + 12|c_{4,k}|µ_k² + 20|c_{5,k}|µ_k³` equals `1 + 168|φ_k|` and is not
`≤ 1 + 150|φ_k|`, and the cited inequality `|φ_k| ≤ 1` fails for small `α_k`; both end bounds are true. -/
theorem second_deriv_bound (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) (mu τ α k),
      |iteratedDeriv 2 (p τ α k) t| ≤ 1 + 150 * |phi τ α k| ∧
        |iteratedDeriv 2 (p τ α k) t| ≤ 1 + 150 * max 1 αhi / αlo := by sorry

end SlowConvergence.SteepestDescent
