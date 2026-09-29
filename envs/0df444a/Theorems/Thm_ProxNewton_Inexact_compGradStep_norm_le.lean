-- Prove2me | Theorems.Thm_ProxNewton_Inexact_compGradStep_norm_le
-- name    : ProxNewton.Inexact.compGradStep_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:38:10.068149+00:00
-- url     : https://prove2.me/theorems/78647def-f8a1-43d3-b402-53c29d8f0a9f
-- title:
--   Lemma 2.2 — $\|G_f(x)\| \le (L_1+1)\|x - x^\star\|$
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable, with $\nabla g$ Lipschitz continuous with constant $L_1\ge0$, let $h$ be a proper closed convex function with domain $D$, and let $x^\star$ be an optimal solution of $\min_x f(x) = g(x)+h(x)$. Then for every $x\in\mathbb R^n$ the composite gradient step with unit step length satisfies
--   $$\|G_f(x)\| \le (L_1+1)\,\|x - x^\star\|.$$
--
--   Thus $G_f$ vanishes at $x^\star$ and grows at most linearly away from it; the local analysis uses this to compare the right-hand side of the stopping condition (2.24) with the distance to $x^\star$.
--
--   **Formalization Note** $G_f$ is `compGradStep g D h 1`; the hypotheses are the standing assumptions of §2 (p. 3).
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 4, Lemma 2.2

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

/-- Lemma 2.2: if `∇g` is Lipschitz continuous with constant `L1`, then
`‖Gf(x)‖ ≤ (L1 + 1) ‖x - x⋆‖` for every `x`. -/
theorem compGradStep_norm_le {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (hxstar : IsMinimizer g D h xstar)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x‖ ≤ (L1 + 1) * ‖x - xstar‖ := by sorry

end ProxNewton.Inexact
