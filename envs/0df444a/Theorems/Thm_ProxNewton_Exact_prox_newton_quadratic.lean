-- Prove2me | Theorems.Thm_ProxNewton_Exact_prox_newton_quadratic
-- name    : ProxNewton.Exact.prox_newton_quadratic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:34:09.435981+00:00
-- url     : https://prove2.me/theorems/2cddbec7-6d25-4454-90d2-6a22a2b0e55a
-- title:
--   Theorem 3.4 — the proximal Newton method converges q-quadratically
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and strongly convex with constant $m>0$, with $\nabla g$ and $\nabla^2 g$ Lipschitz continuous with constants $L_1$ and $L_2$. Let $h$ be a proper closed convex function with domain $D$ and $x^\star$ an optimal solution of $\min f=g+h$. Fix $\alpha\in(0,\tfrac12)$ and $\beta\in(0,1)$, and let $(x_k)$ be a run of the proximal Newton method ($H_k=\nabla^2g(x_k)$). Then $x_k\to x^\star$ and, for all sufficiently large $k$,
--   $$\|x_{k+1}-x^\star\|\le\frac{L_2}{2m}\,\|x_k-x^\star\|^2 .$$
--
--   This extends the classical local quadratic convergence of Newton's method to composite objectives with a nonsmooth convex part.
--
--   **Formalization Note** The paper states $\|x_{k+1}-x^\star\|=O(\|x_k-x^\star\|^2)$; the explicit constant $L_2/(2m)$ is the one derived in its proof (p. 12), so the statement is stronger than the printed $O(\cdot)$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 12, Theorem 3.4 (constant from its proof)

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Theorem 3.4, arXiv:1206.1623v13, p. 12. Under the assumptions of §3.2 (`g` twice
continuously differentiable, strongly convex with constant `m > 0`, `∇g` and `∇²g` Lipschitz with
constants `L1`, `L2`; `h` proper closed convex with domain `D`; `xstar` an optimal solution), every
run of the proximal Newton method with `α ∈ (0, 1/2)` and backtracking factor `β ∈ (0, 1)`
converges to `xstar` q-quadratically: `x k → xstar`, and eventually
`‖x (k+1) − xstar‖ ≤ (L2 / (2m)) ‖x k − xstar‖²` (the constant derived in the proof, p. 12). -/
theorem prox_newton_quadratic {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hL2 : 0 ≤ L2)
    (hHL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinimizer g D h xstar)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonRun g D h α β x H Δ t) :
    Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ L2 / (2 * m) * ‖x k - xstar‖ ^ 2 := by sorry

end ProxNewton.Exact
