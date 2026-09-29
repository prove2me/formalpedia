-- Prove2me | Theorems.Thm_ProxNewton_Exact_optimal_iff_direction_zero
-- name    : ProxNewton.Exact.optimal_iff_direction_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:32:06.298252+00:00
-- url     : https://prove2.me/theorems/f23d35a4-b633-4313-9d2c-eddf7e79a073
-- title:
--   Proposition 2.5 — optimality iff the search direction vanishes
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable with $\nabla g$ Lipschitz continuous with constant $L_1\ge0$, and let $h$ be a proper closed convex function with domain $D$. Let $x\in D$, let $H$ be symmetric positive definite, and let $\Delta x$ be the search direction (2.9) at $x$ with $H$. Then
--   $$x \text{ minimizes } f=g+h \text{ over } D \iff \Delta x=0.$$
--
--   The proximal Newton-type search direction therefore plays the role of the gradient in smooth optimization: its vanishing characterizes optimal solutions of the composite problem.
--
--   **Formalization Note** "Optimal solution" means $x\in D$ and $g(x)+h(x)\le g(y)+h(y)$ for all $y\in D$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 6, Proposition 2.5

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Proposition 2.5, arXiv:1206.1623v13, p. 6. Under the §2 standing assumptions, let `H`
be symmetric positive definite, `x ∈ D`, and `Δ` the search direction (2.9) at `x` with `H`.
Then `x` is an optimal solution of (1.1) if and only if `Δ = 0`. -/
theorem optimal_iff_direction_zero {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsPosDef H) (hΔ : IsSearchDirection g D h x H Δ) :
    IsMinimizer g D h x ↔ Δ = 0 := by sorry

end ProxNewton.Exact
