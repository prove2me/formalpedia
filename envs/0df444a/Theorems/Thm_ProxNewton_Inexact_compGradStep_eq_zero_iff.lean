-- Prove2me | Theorems.Thm_ProxNewton_Inexact_compGradStep_eq_zero_iff
-- name    : ProxNewton.Inexact.compGradStep_eq_zero_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:37:43.74269+00:00
-- url     : https://prove2.me/theorems/ff824f48-6c28-4a4d-ad07-5e6a91668486
-- title:
--   §2.1 property 3 — $G_f(x) = 0$ iff $x$ minimizes $f$
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable with $\nabla g$ Lipschitz continuous with constant $L_1\ge0$, and let $h$ be a proper closed convex function with domain $D$. Write $f = g + h$ and $G_f(x) = x - \operatorname{prox}_h(x - \nabla g(x))$ for the composite gradient step with unit step length. Then for every $x\in\mathbb R^n$,
--   $$G_f(x) = 0 \iff x \text{ minimizes } f,$$
--   that is, $x \in D$ and $f(x)\le f(y)$ for all $y\in D$.
--
--   The length of $G_f(x)$ therefore measures optimality of $x$ in the composite setting, generalizing the condition $\nabla g(x) = 0$ for smooth problems.
--
--   **Formalization Note** $G_f$ is `compGradStep g D h 1`. The hypotheses are the standing assumptions of §2 (p. 3); the Lipschitz constant is carried because §2 assumes it.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 4, §2.1, property 3 of the composite gradient step

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

/-- §2.1, property 3 of the composite gradient step (p. 4): under the standing assumptions of §2,
`Gf(x) = 0` if and only if `x` minimizes `f = g + h`. -/
theorem compGradStep_eq_zero_iff {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (x : EuclideanSpace ℝ (Fin n)) :
    compGradStep g D h 1 x = 0 ↔ IsMinimizer g D h x := by sorry

end ProxNewton.Inexact
