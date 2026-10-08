-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_corollary_B_1
-- name    : RelaxedPRS.DRSSmooth.corollary_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:24.658879+00:00
-- url     : https://prove2.me/theorems/f6794285-e88b-4827-894a-726b68e0cead
-- title:
--   Corollary B.1, p. 33 — joint descent theorem
-- statement:
--   Let $f:H\to(-\infty,+\infty]$ be proper, closed and convex, and let $g:H\to\mathbb R$ be convex and differentiable with $(1/\beta)$-Lipschitz gradient, $\beta>0$. For $x,y\in\operatorname{dom}f$, $w\in H$, and $u\in\partial f(x)$,
--   $$f(x)+g(x)\le f(y)+g(y)+\langle x-y,\nabla g(w)+u\rangle+\frac{\|w-x\|^2}{2\beta}.$$
--   This joint descent inequality combines the smooth and nonsmooth parts of the objective and supports the fundamental DRS estimate.
--
--   **Formalization Note** The subgradient is the published affine-minorant predicate; domain membership is explicit because Lean's extended-real conversion has a default on infinite values.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 33, Corollary B.1 (B.2)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Corollary B.1, p. 33, (B.2), the joint descent theorem. -/
theorem corollary_B_1 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g) :
    ∀ x y w u : H, f x ≠ ⊤ → f y ≠ ⊤ →
      u ∈ MoreauProx.Characterization.subgrad f x →
      (f x).toReal + g x ≤ (f y).toReal + g y +
        inner ℝ (x - y) (gradient g w + u) +
        1 / (2 * β) * ‖w - x‖ ^ 2 := by sorry

end RelaxedPRS.DRSSmooth
