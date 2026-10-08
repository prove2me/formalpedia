-- Prove2me | Theorems.Thm_PenaltyLag_Exact_stationary_at_dual_optimal
-- name    : PenaltyLag.Exact.stationary_at_dual_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:00.284258+00:00
-- url     : https://prove2.me/theorems/9d0f1f30-3f2b-4c0d-a52e-be7858d15b9e
-- title:
--   Proof of Theorem 3.5 — at a dual optimal $\bar y$, a minimizer $\bar x$ of $L_r(\cdot, \bar y)$ has $\nabla_y L_r(\bar x, \bar y) = 0$ and maximizes in $y$
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program (P). Let $r > 0$, let $\bar y \in \mathbb R^m$ be an optimal solution to the dual problem $(D_r)$ (maximize $g_r(y) = \inf_{x \in X} L_r(x, y)$ over $\mathbb R^m$), and let $\bar x \in X$ minimize $L_r(\cdot, \bar y)$ over $X$. Then the function $y \mapsto L_r(\bar x, y)$ is differentiable at $\bar y$ with
--   $$
--   \nabla_y L_r(\bar x, \bar y) = 0,
--   $$
--   and $\bar y$ maximizes $L_r(\bar x, y)$ over all $y \in \mathbb R^m$.
--
--   In the paper this is the step of the proof of Theorem 3.5 that follows from Theorem 3.2: $\nabla_y L_r(\bar x, \bar y) = \nabla g_r(\bar y) = 0$, and the concavity of $L_r(\bar x, \cdot)$ turns stationarity into maximality, so that $(\bar x, \bar y)$ is a saddle point.
--
--   **Formalization Note** The standing assumption of p. 358 is a hypothesis. "Optimal solution to $(D_r)$" means $g_r(\bar y) = \sup_y g_r(y) > -\infty$. The gradient statement is `HasGradientAt … 0 ȳ` in `EuclideanSpace ℝ (Fin m)`, which asserts differentiability as well as the value of the gradient. No sign restriction is placed on $\bar y$.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), proof of Theorem 3.5, pp. 362–363

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Proof of Theorem 3.5, pp. 362–363: if ȳ is an optimal solution to (D_r), r > 0, and
x̄ ∈ X minimizes L_r(·, ȳ) over X, then ∇_y L_r(x̄, ȳ) = 0 and ȳ maximizes L_r(x̄, ·) over ℝ^m. -/
theorem stationary_at_dual_optimal {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : PenaltyLag.Asymptotic.Mult m) (hybar : IsDualOptimal X f₀ f r ybar)
    (xbar : E) (hxbar : xbar ∈ X) (hmin : ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar) :
    HasGradientAt (fun y => PenaltyLag.Asymptotic.Lr f₀ f r xbar y) 0 ybar ∧ ∀ y, PenaltyLag.Asymptotic.Lr f₀ f r xbar y ≤ PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar := by sorry

end PenaltyLag.Exact
