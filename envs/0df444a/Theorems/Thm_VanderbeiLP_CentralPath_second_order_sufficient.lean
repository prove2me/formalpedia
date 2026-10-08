-- Prove2me | Theorems.Thm_VanderbeiLP_CentralPath_second_order_sufficient
-- name    : VanderbeiLP.CentralPath.second_order_sufficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:20:34.920908+00:00
-- url     : https://prove2.me/theorems/9a6493d7-902c-442f-8f9d-c0f447ad8683
-- title:
--   Theorem 17.1 — second-order sufficient condition under linear constraints
-- statement:
--   Consider the equality-constrained problem "maximize $f(x)$ subject to $g_i(x) = 0$, $i = 1, \dots, m$" over $x \in \mathbb{R}^n$, where the constraints are linear: $g_i(x) = G_i^T x - \beta_i$ for vectors $G_1, \dots, G_m \in \mathbb{R}^n$ and scalars $\beta_1, \dots, \beta_m$, so that $\nabla g_i \equiv G_i$. Let $x^*$ be a point at which $f$ is twice differentiable. Suppose $x^*$ is a **critical point** in the sense of (17.3): there are Lagrange multipliers $y_1, \dots, y_m \in \mathbb{R}$ with
--
--   $$g(x^*) = 0, \qquad \nabla f(x^*) = \sum_{i=1}^m y_i \nabla g_i(x^*).$$
--
--   Write $H_f(x^*) = \big(\partial^2 f / \partial x_i \partial x_j\big)(x^*)$ for the Hessian. If
--
--   $$\xi^T H_f(x^*) \xi < 0 \qquad \text{for each } \xi \ne 0 \text{ satisfying } \xi^T \nabla g_i(x^*) = 0,\ i = 1, \dots, m,$$
--
--   then $x^*$ is a local maximum of $f$ on the feasible set $\{x : g(x) = 0\}$: there is a neighbourhood $U$ of $x^*$ with $f(x) \le f(x^*)$ for every feasible $x \in U$.
--
--   In the chapter this is the tool that shows the barrier problem has at most one critical point (the barrier Hessian is diagonal with negative entries).
--
--   **Formalization Note** The constraints are $Gx = \beta$ for an $m \times n$ matrix $G$ with rows $G_i$. "Twice differentiable at $x^*$" is: $f$ is (Fréchet) differentiable at every point of a neighbourhood of $x^*$, and its derivative $x \mapsto Df(x)$ is differentiable at $x^*$; the quadratic form $\xi^T H_f(x^*)\xi$ is $D^2 f(x^*)(\xi)(\xi)$. The gradient condition is stated as an identity of linear functionals: $Df(x^*)v = \sum_i y_i\, G_i^T v$ for all $v$. The local maximum is relative to the feasible set, not to all of $\mathbb{R}^n$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 261–262, Theorem 17.1 with Eqs. (17.4)–(17.5) (PDF pp. 271–272); critical point: p. 260, Eq. (17.3) (PDF p. 270); "twice differentiable": p. 259 (PDF p. 269)

import Mathlib

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Theorem 17.1 (p. 261). Linear constraints `gᵢ(x) = (G x)ᵢ − βᵢ = 0`, `i = 1, …, m`; `f`
twice differentiable at `x*`. A critical point `x*` in the sense of (17.3) (feasible, and
`∇f(x*) = ∑ᵢ yᵢ ∇gᵢ(x*)` for some multipliers `y`) at which `ξᵀ H_f(x*) ξ < 0` (17.4) for every
`ξ ≠ 0` with `ξᵀ ∇gᵢ(x*) = 0` (17.5) is a local maximum of `f` on the feasible set. -/
theorem second_order_sufficient {m n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ) (xstar : Fin n → ℝ) (y : Fin m → ℝ)
    (hf : ∀ᶠ x in 𝓝 xstar, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) xstar)
    (hfeas : G *ᵥ xstar = β)
    (hcrit : ∀ v : Fin n → ℝ, fderiv ℝ f xstar v = ∑ i, y i * (G i ⬝ᵥ v))
    (hhess : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → (∀ i, ξ ⬝ᵥ G i = 0) →
      fderiv ℝ (fderiv ℝ f) xstar ξ ξ < 0) :
    IsLocalMaxOn f {x | G *ᵥ x = β} xstar := by sorry

end VanderbeiLP.CentralPath
