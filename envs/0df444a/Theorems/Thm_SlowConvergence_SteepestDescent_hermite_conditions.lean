-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_hermite_conditions
-- name    : SlowConvergence.SteepestDescent.hermite_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:48.384907+00:00
-- url     : https://prove2.me/theorems/e7c1b91d-42c7-4873-93a2-1a7b9b5beb52
-- title:
--   §2 (2.12)–(2.14), p. 4 — the quintic $p_k$ with coefficients (2.14) meets the Hermite conditions on $[0,\mu_k]$
-- statement:
--   Let $0 < \tau < 1$, $\eta = \tau/(4-2\tau)$, and let the step lengths satisfy (2.6): $0 < \underline\alpha \le \alpha_k \le \overline\alpha < 2$ for all $k$. Let $\mu_k = \alpha_k (1/(k+1))^{\frac12+\eta}$ and let $p_k$ be the quintic (2.11) with the coefficients $c_{0,k}, c_{1,k}, c_{2,k}$ and (2.14). Then for every $k \ge 0$:
--
--   1. $p_k(0) = \alpha_k\big(1-\tfrac12\alpha_k\big)\big(\tfrac{1}{k+1}\big)^{1+2\eta}$ and $p_k(\mu_k) = 0$ (2.12);
--   2. $p_k'(0) = -\big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$ and $p_k'(\mu_k) = -\big(\tfrac{1}{k+2}\big)^{\frac12+\eta}$ (2.13);
--   3. $p_k''(0) = p_k''(\mu_k) = 1$.
--
--   These six conditions are what make the glued function $f_1(x) = p_k(x-x_k) + f_{k+1}$ twice continuously differentiable with $f_1(x_k) = f_k$, $f_1'(x_k) = g_k$ and $f_1''(x_k) = H_k = 1$.
--
--   **Formalization Note** Derivatives are Mathlib's `deriv` and `iteratedDeriv 2` of the polynomial function $p_k$ on $\mathbb R$. The page writes the remaining conditions as a $3\times3$ linear system whose printed right-hand side "$p_k'(\mu_k)$" abbreviates the residual $p_k'(\mu_k) - c_{1,k} - \mu_k$; the interpolation conditions themselves are stated instead of that system.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, (2.11)–(2.15)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, (2.11)–(2.15), p. 4: under (2.6), the quintic
`p_k` with coefficients `c_{0,k}, c_{1,k}, c_{2,k}` and (2.14) satisfies the Hermite conditions on
`[0, µ_k]`: `p_k(0) = α_k(1 − ½α_k)(1/(k+1))^{1+2η}`, `p_k(µ_k) = 0` (2.12),
`p_k'(0) = −(1/(k+1))^{1/2+η}`, `p_k'(µ_k) = −(1/(k+2))^{1/2+η}` (2.13), and
`p_k''(0) = p_k''(µ_k) = 1`. -/
theorem hermite_conditions (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) (k : ℕ) :
    p τ α k 0 = α k * (1 - 1 / 2 * α k) * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ) ∧
      p τ α k (mu τ α k) = 0 ∧
      deriv (p τ α k) 0 = -((1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      deriv (p τ α k) (mu τ α k) = -((1 / ((k : ℝ) + 2)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)) ∧
      iteratedDeriv 2 (p τ α k) 0 = 1 ∧
      iteratedDeriv 2 (p τ α k) (mu τ α k) = 1 := by sorry

end SlowConvergence.SteepestDescent
