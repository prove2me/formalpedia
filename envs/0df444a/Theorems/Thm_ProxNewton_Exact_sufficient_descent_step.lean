-- Prove2me | Theorems.Thm_ProxNewton_Exact_sufficient_descent_step
-- name    : ProxNewton.Exact.sufficient_descent_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:32:29.742014+00:00
-- url     : https://prove2.me/theorems/64f1c4d8-75e8-40ea-ab27-ce695529a3c8
-- title:
--   Lemma 2.6 — step lengths $t\le\min\{1,(2m/L_1)(1-\alpha)\}$ satisfy sufficient descent
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable with $\nabla g$ Lipschitz continuous with constant $L_1\ge0$, and let $h$ be a proper closed convex function with domain $D$; write $f=g+h$. Let $H$ be symmetric with $H\succeq mI$ for some $m>0$, let $x\in D$, let $\Delta x$ be the search direction (2.9) at $x$ with $H$, and let $\lambda=\nabla g(x)^T\Delta x+h(x+\Delta x)-h(x)$. Let $\alpha\in(0,\tfrac12)$. Then every step length
--   $$0<t\le\min\Big\{1,\ \frac{2m}{L_1}(1-\alpha)\Big\} \qquad (2.21)$$
--   satisfies the sufficient descent condition (2.19):
--   $$f(x+t\Delta x)\le f(x)+\alpha t\lambda.$$
--
--   This lemma guarantees that the backtracking line search of Algorithm 1 terminates and that its step lengths stay bounded away from zero.
--
--   **Formalization Note** The bound (2.21) is written without division as $t\le1$ and $L_1t\le2m(1-\alpha)$; this also covers $L_1=0$, where the paper's quotient is read as $+\infty$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 8, Lemma 2.6, Eq. (2.21)

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Lemma 2.6, arXiv:1206.1623v13, p. 8. Under the §2 standing assumptions, suppose
`H ⪰ mI` (symmetric) with `m > 0` and `∇g` is Lipschitz with constant `L1`. Let `x ∈ D`, `Δ` the
search direction (2.9), and `α ∈ (0, 1/2)`. Then every step length `t` with
`0 < t ≤ min {1, (2m/L1)(1 − α)}` satisfies the sufficient descent condition (2.19); the bound is
written division-free as `t ≤ 1 ∧ L1 * t ≤ 2m(1 − α)`. -/
theorem sufficient_descent_step {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 m α : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h) (hm : 0 < m) (hα : 0 < α) (hα2 : α < 1 / 2)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsLowerBounded H m) (hΔ : IsSearchDirection g D h x H Δ) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → L1 * t ≤ 2 * m * (1 - α) →
      SufficientDescent g D h α x Δ t := by sorry

end ProxNewton.Exact
