-- Prove2me | Theorems.Thm_SlowConvergence_Newton_p_second_deriv_bound
-- name    : SlowConvergence.Newton.p_second_deriv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:49.164434+00:00
-- url     : https://prove2.me/theorems/59c66fa4-8d97-40be-91a1-0c3efa395e23
-- title:
--   §2 (2.17), p. 5, at $\alpha_k = 1$ — $|p_k''(t)| \le 1 + 150|\phi_k| \le 151$ on $[0, \mu_k]$
-- statement:
--   Let $0 < \tau < 1$ and let $p_k$, $\mu_k$ and $\phi_k = -\psi_k$ be as in the case $\alpha_k = 1$ of §2. Then for every $k \ge 0$ and every $t \in [0, \mu_k]$
--   $$|p_k''(t)| \;\le\; 1 + 150\,|\phi_k| \;\le\; 151 .$$
--   The last bound is $1 + 150\max[1,\bar\alpha]/\underline\alpha$ of (2.17) with $\underline\alpha = \bar\alpha = 1$.
--
--   This is the uniform bound on the second derivative of the first-coordinate function $f_{2,1}$, half of the statement that $f_2$ has a uniformly bounded Hessian (p. 8).
--
--   **Formalization Note** Only the outer inequalities of the printed chain (2.17) are stated. Its middle line, $2|c_{2,k}| + 6|c_{3,k}|\mu_k + 12|c_{4,k}|\mu_k^2 + 20|c_{5,k}|\mu_k^3 \le 1 + 150|\phi_k|$, is not true as printed (by (2.14) the left side equals $1 + 168|\phi_k|$), but the bound $|p_k''(t)| \le 1 + 150|\phi_k|$ itself holds.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 5, §2, (2.17); used at α_k = 1 in §3, pp. 7–8

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, (2.17), p. 5, in the case `α_k = 1` used for
`f_{2,1} = f_1` (§3, p. 7): for all `k ≥ 0` and all `t ∈ [0, µ_k]`,
`|p_k''(t)| ≤ 1 + 150|φ_k| ≤ 1 + 150 max[1, ᾱ]/α̲`, and with `α_k ≡ 1` (so `α̲ = ᾱ = 1`) the last
bound is `151`.

Formalization Note: only the outer inequalities of the printed chain are stated; the middle line
`2|c_{2,k}| + 6|c_{3,k}|µ_k + 12|c_{4,k}|µ_k² + 20|c_{5,k}|µ_k³ ≤ 1 + 150|φ_k|` is not true as printed
(the left side equals `1 + 168|φ_k|`), but the end-to-end bound is. -/
theorem p_second_deriv_bound (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    (∀ t ∈ Set.Icc (0 : ℝ) (mu τ k), |deriv (deriv (p τ k)) t| ≤ 1 + 150 * |phi τ k|) ∧
      1 + 150 * |phi τ k| ≤ 151 := by sorry

end SlowConvergence.Newton
