-- Prove2me | Theorems.Thm_ProxNewton_Exact_global_convergence
-- name    : ProxNewton.Exact.global_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:32:59.0671+00:00
-- url     : https://prove2.me/theorems/54fa705c-5244-4ee0-ae48-5311dbbb1c1f
-- title:
--   Theorem 3.1 (in the setting of §3.3) — global convergence of proximal Newton-type methods
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be twice continuously differentiable and strongly convex with constant $m>0$, with $\nabla g$ Lipschitz continuous with constant $L_1$. Let $h$ be a proper closed convex function with domain $D$, and let $x^\star$ be an optimal solution of $\min f=g+h$. Fix $\alpha\in(0,\tfrac12)$ and a backtracking factor $\beta\in(0,1)$, and let $M\ge m$. Let $(x_k,H_k,\Delta x_k,t_k)$ be a run of Algorithm 1 from any $x_0\in D$ in which the subproblems (2.9) are solved exactly and
--   $$mI\preceq H_k\preceq MI\quad\text{for all }k.$$
--   Then $x_k\to x^\star$.
--
--   This is the global convergence result on which the local analysis of the proximal Newton and proximal quasi-Newton methods rests.
--
--   **Formalization Note** **Required repair.** As printed (only $H_k\succeq mI$, $f$ closed convex with attained infimum) the theorem is false: take $n=1$, $g(x)=x^2/2$, $h=0$, $m=1$ and $H_k=2^{k+1}$; then $\Delta x_k=-x_k/2^{k+1}$, the unit step satisfies (2.19) for every $\alpha\in(0,\tfrac12)$, and $x_k\to x_0\prod_{j\ge1}(1-2^{-j})\approx0.289\,x_0\ne0=x^\star$. The statement is therefore made in the setting of §3.3 (strongly convex $g$, $mI\preceq H_k\preceq MI$), where the minimizer is unique and the conclusion is convergence to it.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 10, Theorem 3.1 (restated under the assumptions of §3.3, p. 13)

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Theorem 3.1 (in the setting of §3.3), arXiv:1206.1623v13, p. 10. **Repaired statement.**
Let `g` be twice continuously differentiable and strongly convex with constant `m > 0`, with `∇g`
Lipschitz with constant `L1`; let `h` be proper closed convex with domain `D`, and `xstar` an
optimal solution of (1.1). Let `(x, H, Δ, t)` be a run of Algorithm 1 with `α ∈ (0, 1/2)` and
backtracking factor `β ∈ (0, 1)` (subproblems solved exactly), with `mI ⪯ H k ⪯ MI` for all `k`,
`0 < m ≤ M`. Then `x k → xstar` from any `x 0 ∈ D`. As printed, without the upper bound
`H k ⪯ MI`, the theorem is false (n = 1, g x = x²/2, h = 0, m = 1, H k = 2^(k+1): the unit step
is accepted and the iterates converge to about 0.289 · x 0 ≠ 0). -/
theorem global_convergence {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m M L1 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinimizer g D h xstar)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1) (hmM : m ≤ M)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H Δ t)
    (hHb : ∀ k : ℕ, IsBoundedBetween (H k) m M) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end ProxNewton.Exact
