-- Prove2me | Theorems.Thm_TikhonovHDD_Ergodic_theorem_4_2
-- name    : TikhonovHDD.Ergodic.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:28.173495+00:00
-- url     : https://prove2.me/theorems/e02df148-3f12-4e9b-a6ce-0353be52502f
-- title:
--   Theorem 4.2 — strong ergodic convergence to the minimum-norm minimizer when ∫ ε(t)/t dt = +∞
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\beta\ge0$, and let $g$ and $\epsilon$ satisfy the General assumption: $g:\mathcal H\to\mathbb R$ is convex, twice Fréchet differentiable, with gradient Lipschitz continuous on bounded sets and $\operatorname{argmin} g\ne\emptyset$; $\epsilon:[t_0,+\infty)\to[0,+\infty)$ is nonincreasing, of class $C^1$, with $\lim_{t\to+\infty}\epsilon(t)=0$. Let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad t\ge t_0,\quad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   Assume
--   $$
--   \int_{t_0}^{+\infty}\frac{\epsilon(t)}{t}\,dt=+\infty,
--   $$
--   and let $x^*=\operatorname{argmin}\{\|x\|:x\in\operatorname{argmin} g\}$ be the element of minimum norm of the nonempty closed convex set $\operatorname{argmin} g$. If $\alpha>0$, then
--   $$
--   \lim_{t\to+\infty}\frac{1}{\int_{t_0}^{t}\frac{\epsilon(s)}{s}\,ds}\int_{t_0}^{t}\frac{\epsilon(s)}{s}\|x(s)-x^*\|^2\,ds=0
--   \qquad\text{and}\qquad
--   \liminf_{t\to+\infty}\|x(t)-x^*\|=0 .
--   $$
--
--   When the Tikhonov parameter decays slowly enough that $\int\epsilon(t)/t\,dt$ diverges, the trajectory converges strongly in this weighted ergodic sense to the minimum-norm minimizer, extending the corresponding result for the system without Hessian damping.
--
--   **Formalization Note** The statement is made for every global $C^2$-solution; existence and uniqueness are Theorem 2.1 of the paper. The hypothesis $\alpha>0$ is the theorem's own and replaces the standing $\alpha\ge3$ of (5). Divergence of the integral is $\int_{t_0}^{T}\frac{\epsilon(t)}{t}\,dt\to+\infty$ as $T\to+\infty$. The ergodic average is written with the reciprocal of $\int_{t_0}^t\frac{\epsilon(s)}{s}\,ds$, which vanishes for $t\ge t_0$ only at $t=t_0$ (the divergence hypothesis forces $\epsilon>0$ on $[t_0,+\infty)$); the value there does not affect the limit. "$\liminf\|x(t)-x^*\|=0$" is stated as: for every $\delta>0$ there are arbitrarily large $t$ with $\|x(t)-x^*\|<\delta$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 18, Theorem 4.2

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhonovHDD.Ergodic

/-- Theorem 4.2 (p. 18): if `∫_{t₀}^{+∞} ε(t)/t dt = +∞` and `α > 0`, every global
`C²`-solution of (5) converges strongly in the ergodic sense to the minimum-norm element `x⋆`
of `argmin g`:
`(∫_{t₀}^{t} ε(s)/s ds)⁻¹ ∫_{t₀}^{t} ε(s)/s ‖x(s) − x⋆‖² ds → 0`, and
`lim inf_{t → +∞} ‖x(t) − x⋆‖ = 0` (stated as: for every `δ > 0`, `‖x(t) − x⋆‖ < δ` for
arbitrarily large `t`). -/
theorem theorem_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd)
    (hdiv : Tendsto (fun T => ∫ t in t₀..T, ε t / t) atTop atTop)
    (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar) :
    Tendsto (fun t => (∫ s in t₀..t, ε s / s)⁻¹ * ∫ s in t₀..t, ε s / s * ‖x s - xstar‖ ^ 2)
        atTop (𝓝 0) ∧
      ∀ δ > 0, ∃ᶠ t in atTop, ‖x t - xstar‖ < δ := by sorry

end TikhonovHDD.Ergodic
