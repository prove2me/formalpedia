-- Prove2me | Theorems.Thm_ProxNewton_Exact_search_direction_properties
-- name    : ProxNewton.Exact.search_direction_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:31:30.959212+00:00
-- url     : https://prove2.me/theorems/73264c65-7067-4e9f-9b43-ddb7fc97fe50
-- title:
--   Proposition 2.4 — search direction properties (2.14), (2.15)
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable with $\nabla g$ Lipschitz continuous with constant $L_1\ge0$, and let $h$ be a proper closed convex function with domain $D$; write $f=g+h$. Let $x\in D$, let $H$ be a symmetric positive definite matrix, and let $\Delta x$ be the proximal Newton-type search direction (2.9) at $x$ with $H$. Put $\lambda=\nabla g(x)^T\Delta x+h(x+\Delta x)-h(x)$ and $x_+=x+t\Delta x$. Then
--
--   1. there is a constant $C$ such that for every $t\in(0,1]$
--   $$f(x_+)\le f(x)+t\lambda+Ct^2, \qquad (2.14)$$
--   2. and
--   $$\lambda\le-\Delta x^TH\Delta x. \qquad (2.15)$$
--
--   Together, (2.14) and (2.15) say that $\Delta x$ is a descent direction for $f$; (2.15) is the inequality used in every later convergence proof.
--
--   **Formalization Note** The $O(t^2)$ of (2.14) is stated as an explicit bound $Ct^2$ on $t\in(0,1]$, the range on which the paper's proof works. The left side is the extended-valued objective, so the bound also asserts $x_+\in D$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 6, Proposition 2.4, Eqs. (2.14)–(2.15)

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Proposition 2.4 (search direction properties), arXiv:1206.1623v13, p. 6. Under the §2
standing assumptions (`g` convex, continuously differentiable, `∇g` Lipschitz with constant `L1`;
`h` proper closed convex with domain `D`), let `x ∈ D`, `H` symmetric positive definite, and `Δ`
the search direction (2.9). Then (2.14) `f(x + tΔ) ≤ f(x) + tλ + O(t²)`, in the form
`∃ C, ∀ t ∈ (0, 1], f(x + tΔ) ≤ f(x) + tλ + C t²`; and (2.15) `λ ≤ −ΔᵀHΔ`. -/
theorem search_direction_properties {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsPosDef H) (hΔ : IsSearchDirection g D h x H Δ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      compositeObj g D h (x + t • Δ) ≤
        ((g x + h x + t * predDecrease g h x Δ + C * t ^ 2 : ℝ) : EReal)) ∧
    predDecrease g h x Δ ≤ -⟪H Δ, Δ⟫ := by sorry

end ProxNewton.Exact
