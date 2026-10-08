-- Prove2me | Theorems.Thm_TikhonovHDD_Ergodic_eq_46
-- name    : TikhonovHDD.Ergodic.eq_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:15.321483+00:00
-- url     : https://prove2.me/theorems/efc7baa7-9009-4b94-966e-7cb4825a1c58
-- title:
--   (46), p. 20 — ∫_{t₀}^{t} (ε(s)/s)(h_{x*}(s) − ½(‖x*‖² − ‖x_{ε(s)}‖²)) ds ≤ C
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha>0$, $\beta\ge0$, and let $g$ and $\epsilon$ satisfy the General assumption. Let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0,
--   $$
--   and assume $\int_{t_0}^{+\infty}\frac{\epsilon(t)}{t}\,dt=+\infty$. Let $x^*$ be the element of minimum norm of $\operatorname{argmin} g$, $h_{x^*}(t)=\tfrac12\|x(t)-x^*\|^2$, and for $\epsilon>0$ let $x_\epsilon$ be the minimizer of $g+\frac\epsilon2\|\cdot\|^2$. Then there exists $C>0$ such that
--   $$
--   \int_{t_0}^{t}\frac{\epsilon(s)}{s}\Big(h_{x^*}(s)-\frac12\big(\|x^*\|^2-\|x_{\epsilon(s)}\|^2\big)\Big)\,ds\le C\qquad\text{for every }t\ge t_0 .
--   $$
--
--   This is the last estimate of the proof of Theorem 4.2 before the l'Hospital step: dividing by $\int_{t_0}^t\frac{\epsilon(s)}{s}\,ds\to+\infty$ yields the ergodic convergence.
--
--   **Formalization Note** The curve $\epsilon\mapsto x_\epsilon$ is a selection required to minimize $g+\frac\epsilon2\|\cdot\|^2$ for every $\epsilon>0$. The integrand evaluates it only at $\epsilon(s)$, and $\epsilon(s)>0$ for every $s\ge t_0$ under the divergence hypothesis (if $\epsilon(T)=0$, then $\epsilon\equiv0$ on $[T,+\infty)$ and the integral would converge). The divergence hypothesis is stated as $\int_{t_0}^{T}\frac{\epsilon(t)}{t}\,dt\to+\infty$ as $T\to+\infty$. The integrals are oriented integrals over $[t_0,t]$; the integrand is continuous there.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 20, §4.1, proof of Theorem 4.2, (46)

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhonovHDD.Ergodic

/-- (46), §4.1, p. 20 (proof of Theorem 4.2): under the hypotheses of Theorem 4.2 there is
`C > 0` with
`∫_{t₀}^{t} ε(s)/s (h_{x⋆}(s) − ½(‖x⋆‖² − ‖x_{ε(s)}‖²)) ds ≤ C` for every `t ≥ t₀`,
where `x_e` is the Tikhonov approximation curve. -/
theorem eq_46 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (xε : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd)
    (hdiv : Tendsto (fun T => ∫ t in t₀..T, ε t / t) atTop atTop)
    (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar)
    (hxε : ∀ e > 0, IsTikhonovPoint g e (xε e)) :
    ∃ C > 0, ∀ t ≥ t₀,
      ∫ s in t₀..t, ε s / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖xε (ε s)‖ ^ 2))
        ≤ C := by sorry

end TikhonovHDD.Ergodic
