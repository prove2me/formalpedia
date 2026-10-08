-- Prove2me | Theorems.Thm_TikhonovHDD_Ergodic_tikhonov_curve_tendsto
-- name    : TikhonovHDD.Ergodic.tikhonov_curve_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:25.45359+00:00
-- url     : https://prove2.me/theorems/91b89a15-4f1b-4295-a9cb-7ae99e6d4950
-- title:
--   §4, p. 18 — the Tikhonov curve satisfies lim_{ε→0} x_ε = x*
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and let $g:\mathcal H\to\mathbb R$ satisfy the General assumption (convex, twice Fréchet differentiable, gradient Lipschitz on bounded sets, $\operatorname{argmin} g\ne\emptyset$). Let $x^*$ be the element of minimum norm of the nonempty closed convex set $\operatorname{argmin} g$, and for $\epsilon>0$ let $x_\epsilon$ be the unique minimizer of $g+\frac{\epsilon}{2}\|\cdot\|^2$. Then the Tikhonov approximation curve converges strongly to $x^*$:
--   $$
--   \lim_{\epsilon\to0^+}x_\epsilon=x^* .
--   $$
--
--   The paper calls this fact well known and uses it in the proof of Theorem 4.2, where $\epsilon(t)\to0$ gives $x_{\epsilon(t)}\to x^*$ and hence $\|x^*\|^2-\|x_{\epsilon(t)}\|^2\to0$.
--
--   **Formalization Note** The curve is a map $\epsilon\mapsto x_\epsilon$ on $\mathbb R$ that is required to be a minimizer of $g+\frac\epsilon2\|\cdot\|^2$ for every $\epsilon>0$; its values for $\epsilon\le0$ are irrelevant, since the limit is taken from the right ($\epsilon\to0^+$). Convergence is in norm.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 18, §4 ("It is well known that the Tikhonov approximation curve ϵ −→ xϵ satisfies limϵ−→0 xϵ = x∗"); used on p. 20

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhonovHDD.Ergodic

/-- §4, p. 18 ("well known"): the Tikhonov approximation curve `ε ↦ x_ε`,
`x_ε = argmin (g + (ε/2)‖·‖²)`, converges in norm to the minimum-norm element `x⋆` of
`argmin g` as `ε → 0⁺`. -/
theorem tikhonov_curve_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (g : H → ℝ) (hg : GeneralAssumptionG g) (xstar : H) (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar)
    (xε : ℝ → H) (hxε : ∀ e > 0, IsTikhonovPoint g e (xε e)) :
    Tendsto xε (𝓝[>] 0) (𝓝 xstar) := by sorry

end TikhonovHDD.Ergodic
