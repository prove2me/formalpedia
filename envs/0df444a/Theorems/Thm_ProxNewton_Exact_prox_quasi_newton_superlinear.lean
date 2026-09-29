-- Prove2me | Theorems.Thm_ProxNewton_Exact_prox_quasi_newton_superlinear
-- name    : ProxNewton.Exact.prox_quasi_newton_superlinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:35:29.976415+00:00
-- url     : https://prove2.me/theorems/184f209b-c6e9-4d0c-b765-3e0e154048e1
-- title:
--   Theorem 3.7 — proximal quasi-Newton methods converge q-superlinearly under the Dennis–Moré criterion
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and strongly convex with constant $m>0$, with $\nabla g$ and $\nabla^2 g$ Lipschitz continuous with constants $L_1$ and $L_2$. Let $h$ be a proper closed convex function (possibly taking the value $+\infty$) with domain $D$, and let $x^\star$ be an optimal solution of
--   $$\min_{x\in\mathbb R^n} f(x)=g(x)+h(x).$$
--   Fix $\alpha\in(0,\tfrac12)$, a backtracking factor $\beta\in(0,1)$, and $M\ge m$. Let $(x_k,H_k,\Delta x_k,t_k)$ be a run of Algorithm 1 (a proximal quasi-Newton method) from any $x_0\in D$ such that $mI\preceq H_k\preceq MI$ for every $k$ and $\{H_k\}$ satisfies the Dennis–Moré criterion
--   $$\frac{\|(H_k-\nabla^2 g(x^\star))(x_{k+1}-x_k)\|}{\|x_{k+1}-x_k\|}\to0 .$$
--   Then $x_k$ converges to $x^\star$ q-superlinearly:
--   $$x_k\to x^\star\quad\text{and}\quad \|x_{k+1}-x^\star\|=o(\|x_k-x^\star\|).$$
--
--   This is the composite counterpart of the Dennis–Moré characterization of superlinear convergence of quasi-Newton methods, and it covers proximal BFGS and L-BFGS-type methods whenever their Hessian approximations satisfy the criterion.
--
--   **Formalization Note** The little-$o$ is stated without quotients: for every $\varepsilon>0$, eventually $\|x_{k+1}-x^\star\|\le\varepsilon\|x_k-x^\star\|$. The line search is backtracking from the unit step with factor $\beta$ (the least $j$ with $\beta^j$ satisfying (2.19)); a line search allowed to return any admissible step would make the theorem false. The same constant $m$ bounds $g$'s strong convexity and $H_k$ from below, as printed.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 14, Theorem 3.7

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Theorem 3.7, arXiv:1206.1623v13, p. 14. Let `g` be twice continuously differentiable and
strongly convex with constant `m > 0`, with `∇g` and `∇²g` Lipschitz with constants `L1`, `L2`;
let `h` be proper closed convex with domain `D`, and `xstar` an optimal solution of (1.1). Let
`(x, H, Δ, t)` be a run of Algorithm 1 (a proximal quasi-Newton method) with `α ∈ (0, 1/2)` and
backtracking factor `β ∈ (0, 1)`, from any `x 0 ∈ D`. If `mI ⪯ H k ⪯ MI` for all `k`, with
`0 < m ≤ M`, and `{H k}` satisfies the Dennis–Moré criterion (3.2), then `x k → xstar`
q-superlinearly: `x k → xstar` and, for every `ε > 0`, eventually
`‖x (k+1) − xstar‖ ≤ ε ‖x k − xstar‖`. -/
theorem prox_quasi_newton_superlinear {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m M L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hL2 : 0 ≤ L2)
    (hHL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinimizer g D h xstar)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1) (hmM : m ≤ M)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H Δ t)
    (hHb : ∀ k : ℕ, IsBoundedBetween (H k) m M)
    (hDM : DennisMore g xstar x H) :
    Tendsto x atTop (𝓝 xstar) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ ε * ‖x k - xstar‖ := by sorry

end ProxNewton.Exact
