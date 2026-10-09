-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_proposition_1_1_a_iii
-- name    : RelSmoothFOM.DOptimal.proposition_1_1_a_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:47.904961+00:00
-- url     : https://prove2.me/theorems/902983b2-7531-42ae-8c76-513fecd0e0c3
-- title:
--   Proposition 1.1 (a-iii) ⇒ (a-i) — Hessian domination implies relative smoothness
-- statement:
--   Let $U$ be an open convex region in a finite-dimensional real inner-product space, and let $f$ and $h$ be convex functions differentiable twice on $U$. Fix $L\in\mathbb R$. If $\nabla^2 f(z)\preceq L\nabla^2h(z)$ for every $z\in U$, then for all $x,y\in U$,
--   $$f(y)\le f(x)+\nabla f(x)\cdot(y-x)+L D_h(y,x).$$
--   This is the Hessian criterion for relative smoothness used after the matrix calculation in Proposition 2.2.
--
--   **Formalization Note** $U$ represents the open domain $\operatorname{int}Q$; the statement also carries the section's standing convexity and differentiability assumptions for $f,h$. Twice differentiability is expressed by differentiability of their first Fréchet derivatives.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 336, Proposition 1.1 (a-iii) ⇒ (a-i)

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- Proposition 1.1, (a-iii) implies (a-i), on the open domain int Q. -/
theorem proposition_1_1_a_iii {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Set E) (hU : IsOpen U) (hUc : Convex ℝ U)
    (f h : E → ℝ) (hfc : ConvexOn ℝ U f) (hhc : ConvexOn ℝ U h)
    (hfd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hhd : ∀ x ∈ U, DifferentiableAt ℝ h x)
    (hf2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hh2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ h) x)
    (L : ℝ)
    (hess : ∀ x ∈ U, ∀ v : E,
      fderiv ℝ (fderiv ℝ f) x v v ≤
        L * fderiv ℝ (fderiv ℝ h) x v v) :
    ∀ x ∈ U, ∀ y ∈ U,
      f y ≤ f x + fderiv ℝ f x (y - x) + L * RelSmoothFOM.PrimalGrad.bregman h y x := by sorry

end RelSmoothFOM.DOptimal
