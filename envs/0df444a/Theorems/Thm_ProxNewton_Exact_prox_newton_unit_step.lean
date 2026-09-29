-- Prove2me | Theorems.Thm_ProxNewton_Exact_prox_newton_unit_step
-- name    : ProxNewton.Exact.prox_newton_unit_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:33:38.476315+00:00
-- url     : https://prove2.me/theorems/7ee66b8f-4abc-4d54-8fb0-6d78dfb4b01f
-- title:
--   Lemma 3.3 — the proximal Newton method eventually accepts the unit step
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and strongly convex with constant $m>0$, with $\nabla g$ and $\nabla^2 g$ Lipschitz continuous with constants $L_1$ and $L_2$. Let $h$ be a proper closed convex function with domain $D$, and $f=g+h$. Fix $\alpha\in(0,\tfrac12)$ and $\beta\in(0,1)$, and let $(x_k,\Delta x_k,t_k)$ be a run of the proximal Newton method, i.e. Algorithm 1 with $H_k=\nabla^2 g(x_k)$. Then for all sufficiently large $k$ the unit step satisfies the sufficient decrease condition (2.19):
--   $$f(x_k+\Delta x_k)\le f(x_k)+\alpha\lambda_k,\qquad \lambda_k=\nabla g(x_k)^T\Delta x_k+h(x_k+\Delta x_k)-h(x_k).$$
--
--   Since the line search tries the unit step first, the method eventually takes full steps $x_{k+1}=x_k+\Delta x_k$, which is what the quadratic rate of Theorem 3.4 needs.
--
--   **Formalization Note** The restriction $\alpha<\tfrac12$ is essential: the paper's proof ends with the strict bound $<\tfrac12\lambda_k$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 11, Lemma 3.3

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Lemma 3.3, arXiv:1206.1623v13, p. 11. Let `g` be twice continuously differentiable and
strongly convex with constant `m > 0`, with `∇g` and `∇²g` Lipschitz with constants `L1`, `L2`;
let `h` be proper closed convex with domain `D`. For every run of the proximal Newton method
(`H k = ∇²g(x k)`) with `α ∈ (0, 1/2)` and backtracking factor `β ∈ (0, 1)`, the unit step length
satisfies the sufficient decrease condition (2.19) for all sufficiently large `k`:
`f(x k + Δ k) ≤ f(x k) + α λ k`. -/
theorem prox_newton_unit_step {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hL2 : 0 ≤ L2)
    (hHL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonRun g D h α β x H Δ t) :
    ∀ᶠ k in atTop, SufficientDescent g D h α (x k) (Δ k) 1 := by sorry

end ProxNewton.Exact
