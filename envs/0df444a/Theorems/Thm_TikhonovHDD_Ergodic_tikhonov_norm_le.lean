-- Prove2me | Theorems.Thm_TikhonovHDD_Ergodic_tikhonov_norm_le
-- name    : TikhonovHDD.Ergodic.tikhonov_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:22.968672+00:00
-- url     : https://prove2.me/theorems/1134f188-b612-4081-aa91-5ceaac532bab
-- title:
--   §4, p. 18 — ‖x_ε‖ ≤ ‖x*‖ for every ε > 0
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and let $g:\mathcal H\to\mathbb R$ satisfy the General assumption (convex, twice Fréchet differentiable, gradient Lipschitz on bounded sets, $\operatorname{argmin} g\ne\emptyset$). Let $x^*$ be the element of minimum norm of $\operatorname{argmin} g$. For $\epsilon>0$ let
--   $$
--   x_\epsilon=\operatorname*{argmin}_{x\in\mathcal H}\Big(g(x)+\frac{\epsilon}{2}\|x\|^2\Big).
--   $$
--   Then
--   $$
--   \|x_\epsilon\|\le\|x^*\|\qquad\text{for every }\epsilon>0 .
--   $$
--
--   The Tikhonov approximation curve thus stays in the closed ball of radius $\|x^*\|$. This bound makes the term $\|x^*\|^2-\|x_{\epsilon(s)}\|^2$ in the proof of Theorem 4.2 nonnegative.
--
--   **Formalization Note** $x_\epsilon$ is any point $y$ minimizing $g+\frac\epsilon2\|\cdot\|^2$ (such a point is unique). The hypothesis that $x^*$ has minimum norm is kept as in the paper, although the inequality holds for every minimizer of $g$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 18, §4, display ‖xϵ‖ ≤ ‖x∗‖ for every ϵ > 0 (after the Tikhonov curve)

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhonovHDD.Ergodic

/-- §4, p. 18: for every `ε > 0`, the point `x_ε = argmin (g + (ε/2)‖·‖²)` of the Tikhonov
approximation curve satisfies `‖x_ε‖ ≤ ‖x⋆‖`, where `x⋆` is the minimum-norm element of
`argmin g`. -/
theorem tikhonov_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (g : H → ℝ) (hg : GeneralAssumptionG g) (xstar : H) (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar)
    (e : ℝ) (he : 0 < e) (y : H) (hy : IsTikhonovPoint g e y) :
    ‖y‖ ≤ ‖xstar‖ := by sorry

end TikhonovHDD.Ergodic
