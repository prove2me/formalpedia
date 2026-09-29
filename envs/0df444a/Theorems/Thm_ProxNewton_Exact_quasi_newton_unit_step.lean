-- Prove2me | Theorems.Thm_ProxNewton_Exact_quasi_newton_unit_step
-- name    : ProxNewton.Exact.quasi_newton_unit_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:34:34.10721+00:00
-- url     : https://prove2.me/theorems/3f562da7-fee5-46d9-8112-55a9c49df523
-- title:
--   Lemma 3.5 (Lemma A.1) — proximal quasi-Newton methods eventually accept the unit step
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and strongly convex with constant $m>0$, with $\nabla g$ and $\nabla^2 g$ Lipschitz continuous with constants $L_1$ and $L_2$. Let $h$ be a proper closed convex function with domain $D$ and $x^\star$ an optimal solution of $\min f=g+h$. Fix $\alpha\in(0,\tfrac12)$, $\beta\in(0,1)$ and $M\ge m$, and let $(x_k,H_k,\Delta x_k,t_k)$ be a run of Algorithm 1 such that
--
--   1. $mI\preceq H_k\preceq MI$ for every $k$, and
--   2. $\{H_k\}$ satisfies the Dennis–Moré criterion (3.2): $\|(H_k-\nabla^2 g(x^\star))(x_{k+1}-x_k)\|/\|x_{k+1}-x_k\|\to0$.
--
--   Then, after sufficiently many iterations, the unit step satisfies the sufficient descent condition (2.19):
--   $$f(x_k+\Delta x_k)\le f(x_k)+\alpha\lambda_k .$$
--
--   This is the first ingredient of the superlinear convergence proof of Theorem 3.7.
--
--   **Formalization Note** The paper states the hypotheses on $g$ in Lemma A.1 (p. 23) as (i) $C^2$ and strongly convex, (ii) $\nabla^2g$ Lipschitz; the Lipschitz continuity of $\nabla g$ is the standing assumption of §3.3 (p. 13) and is included. The same constant $m$ bounds $g$'s strong convexity and $H_k$ from below, as printed.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 13, Lemma 3.5; p. 23, Lemma A.1

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Lemma 3.5 (Lemma A.1), arXiv:1206.1623v13, p. 13 and p. 23. Let `g` be twice
continuously differentiable and strongly convex with constant `m > 0`, with `∇g` and `∇²g`
Lipschitz with constants `L1`, `L2`; let `h` be proper closed convex with domain `D`, and `xstar`
an optimal solution. For every run of Algorithm 1 with `α ∈ (0, 1/2)`, backtracking factor
`β ∈ (0, 1)`, `mI ⪯ H k ⪯ MI` (`0 < m ≤ M`) for all `k`, and `{H k}` satisfying the Dennis–Moré
criterion (3.2) at `xstar`, the unit step length satisfies the sufficient descent condition (2.19)
after sufficiently many iterations. -/
theorem quasi_newton_unit_step {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
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
    ∀ᶠ k in atTop, SufficientDescent g D h α (x k) (Δ k) 1 := by sorry

end ProxNewton.Exact
