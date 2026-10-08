-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_lemma_B_1
-- name    : RelaxedPRS.DRSSmooth.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:23.018702+00:00
-- url     : https://prove2.me/theorems/8e7f17a6-ef62-44eb-99aa-fc8b56876442
-- title:
--   Lemma B.1, p. 32 — contraction of gradients at proximal points
-- statement:
--   Let $g:H\to\mathbb R$ be convex and differentiable with $(1/\beta)$-Lipschitz gradient, where $\beta>0$. For $\gamma>0$, let $P_g=\operatorname{prox}_{\gamma g}$. Then for all $x,y\in H$,
--   $$\|\nabla g(P_gx)-\nabla g(P_gy)\|^2\le\frac{\|x-y\|^2}{\gamma^2+\beta^2}.$$
--   This contraction controls changes of the smooth gradient along DRS iterates.
--
--   **Formalization Note** The printed $y^+=\operatorname{prox}_{\gamma f}(y)$ is corrected to $\operatorname{prox}_{\gamma g}(y)$, as required by the proof and the gradient expression.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 32, Lemma B.1 (B.1)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma B.1, p. 32; the printed `prox_{γf}(y)` is corrected to `prox_{γg}(y)`. -/
theorem lemma_B_1 (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pg : H → H)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg) :
    ∀ x y : H,
      ‖gradient g (Pg x) - gradient g (Pg y)‖ ^ 2 ≤
        1 / (γ ^ 2 + β ^ 2) * ‖x - y‖ ^ 2 := by sorry

end RelaxedPRS.DRSSmooth
