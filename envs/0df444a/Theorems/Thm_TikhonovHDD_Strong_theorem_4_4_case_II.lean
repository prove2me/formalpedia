-- Prove2me | Theorems.Thm_TikhonovHDD_Strong_theorem_4_4_case_II
-- name    : TikhonovHDD.Strong.theorem_4_4_case_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:52.02047+00:00
-- url     : https://prove2.me/theorems/ec1e2065-9986-407a-881e-9822f9a05383
-- title:
--   Theorem 4.4, Case II — if $\|x(t)\|<\|x^*\|$ for all large $t$, then $x(t)\to x^*$ strongly
-- statement:
--   Work under the hypotheses of Theorem 4.4. Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha\ge 3$, $\beta\ge 0$, $u_0,v_0\in\mathcal H$, let $g$ and $\epsilon$ satisfy the General assumption, and let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   Assume:
--
--   1. $\int_{t_0}^{+\infty}\frac{\epsilon(t)}{t}\,dt<+\infty$;
--   2. $\displaystyle\lim_{t\to+\infty}\frac{\beta}{\epsilon(t)t^{\frac{\alpha}{3}+1}}\int_{t_0}^{t}\epsilon^2(s)s^{\frac{\alpha}{3}+1}\,ds=0$;
--   3. there exist $a>1$ and $t_1\ge t_0$ with $\dot\epsilon(t)\le-\frac{a\beta}{2}\epsilon^2(t)$ for every $t\ge t_1$;
--   4. if $\alpha=3$: $\lim_{t\to+\infty}t^2\epsilon(t)=+\infty$;
--   5. if $\alpha>3$: there exists $c>0$ with $t^2\epsilon(t)\ge\frac23\alpha\left(\frac13\alpha-1+\beta c^2\right)$ for all $t$ large enough;
--
--   and let $x^*$ be the element of minimum norm of $\operatorname{argmin} g$. If there exists $T\ge t_0$ such that the trajectory $\{x(t):t\ge T\}$ stays in the open ball $B(0,\|x^*\|)$, that is $\|x(t)\|<\|x^*\|$ for every $t\ge T$, then
--   $$
--   \lim_{t\to+\infty}x(t)=x^*
--   $$
--   in the norm of $\mathcal H$.
--
--   This is the second of the three exhaustive cases into which the paper splits the proof of Theorem 4.4.
--
--   **Formalization Note** Stated for every global $C^2$-solution of (5) (existence is Theorem 2.1 of the paper). $t^{\alpha/3+1}$ is the real power. All hypotheses of Theorem 4.4 are kept, as the case lives inside that proof, even though not all of them are needed here.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, §4.2, proof of Theorem 4.4, Case II, pp. 25–26

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting

open Set Filter Topology

namespace TikhonovHDD.Strong

/-- Theorem 4.4, proof, Case II (pp. 25–26): if `‖x(t)‖ < ‖x⋆‖` for all `t ≥ T`
(some `T ≥ t₀`), then `x(t) → x⋆` strongly.
Standing hypotheses (those of Theorem 4.4, arXiv:1911.12845v2, p. 21): the General
assumption, `t₀ > 0`, `α ≥ 3`, `β ≥ 0`, `x` a global `C²`-solution of (5),
`∫_{t₀}^{+∞} ε(t)/t dt < +∞`, `β/(ε(t) t^{α/3+1}) ∫_{t₀}^t ε²(s) s^{α/3+1} ds → 0`,
`ε̇(t) ≤ −(aβ/2) ε²(t)` for `t ≥ t₁` (some `a > 1`, `t₁ ≥ t₀`), for `α = 3`: `t² ε(t) → +∞`,
for `α > 3`: `t² ε(t) ≥ (2/3)α((1/3)α − 1 + βc²)` eventually (some `c > 0`), and `x⋆` the
minimum-norm element of `argmin g`. -/
theorem theorem_4_4_case_II
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd)
    (hε_int : MeasureTheory.IntegrableOn (fun t => ε t / t) (Ici t₀))
    (hε_lim : Tendsto
      (fun t => β / (ε t * t ^ (α / 3 + 1)) * ∫ s in t₀..t, ε s ^ 2 * s ^ (α / 3 + 1))
      atTop (𝓝 0))
    (hε_deriv : ∃ a > (1 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε' t ≤ -(a * β / 2) * ε t ^ 2)
    (hα3 : α = 3 → Tendsto (fun t => t ^ 2 * ε t) atTop atTop)
    (hα3lt : 3 < α → ∃ c > (0 : ℝ),
      ∀ᶠ t in atTop, 2 / 3 * α * (1 / 3 * α - 1 + β * c ^ 2) ≤ t ^ 2 * ε t)
    (hxstar : IsMinNormMinimizer g xstar)
    (hcase : ∃ T ≥ t₀, ∀ t ≥ T, ‖x t‖ < ‖xstar‖) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end TikhonovHDD.Strong
