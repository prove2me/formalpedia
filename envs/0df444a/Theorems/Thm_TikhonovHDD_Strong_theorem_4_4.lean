-- Prove2me | Theorems.Thm_TikhonovHDD_Strong_theorem_4_4
-- name    : TikhonovHDD.Strong.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:52.534245+00:00
-- url     : https://prove2.me/theorems/c6a8c034-c67f-4849-9eca-0654463aad97
-- title:
--   Theorem 4.4 — $\liminf_{t\to+\infty}\|x(t)-x^*\|=0$, and $x(t)\to x^*$ if the trajectory ends inside or outside $B(0,\|x^*\|)$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha\ge 3$, $\beta\ge 0$ and $u_0,v_0\in\mathcal H$. Let $g:\mathcal H\to\mathbb R$ be convex and twice Fréchet differentiable, with gradient Lipschitz continuous on bounded sets and $\operatorname{argmin} g\neq\emptyset$, and let $\epsilon:[t_0,+\infty)\to[0,+\infty)$ be nonincreasing, of class $C^1$, with $\lim_{t\to+\infty}\epsilon(t)=0$. Let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\quad t\ge t_0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   Assume that
--   $$
--   \int_{t_0}^{+\infty}\frac{\epsilon(t)}{t}\,dt<+\infty\qquad\text{and}\qquad\lim_{t\to+\infty}\frac{\beta}{\epsilon(t)t^{\frac{\alpha}{3}+1}}\int_{t_0}^{t}\epsilon^2(s)s^{\frac{\alpha}{3}+1}\,ds=0,
--   $$
--   that there exist $a>1$ and $t_1\ge t_0$ such that $\dot\epsilon(t)\le-\frac{a\beta}{2}\epsilon^2(t)$ for every $t\ge t_1$, and in addition that
--
--   1. in case $\alpha=3$: $\lim_{t\to+\infty}t^2\epsilon(t)=+\infty$;
--   2. in case $\alpha>3$: there exists $c>0$ such that $t^2\epsilon(t)\ge\frac23\alpha\left(\frac13\alpha-1+\beta c^2\right)$ for $t$ large enough.
--
--   If $x^*$ is the element of minimum norm of the nonempty convex closed set $\operatorname{argmin} g$, then
--   $$
--   \liminf_{t\to+\infty}\|x(t)-x^*\|=0 .
--   $$
--   In addition,
--   $$
--   \lim_{t\to+\infty}\|x(t)-x^*\|=0
--   $$
--   if there exists $T\ge t_0$ such that the trajectory $\{x(t):t\ge T\}$ stays either in the open ball $B(0,\|x^*\|)$, or in its complement.
--
--   This is the strong-convergence result for which the Tikhonov term $\epsilon(t)x(t)$ is added to the Hessian-damped inertial dynamics: without it, trajectories are only known to converge weakly to some minimizer, while here they approach the distinguished minimizer of minimum norm.
--
--   **Formalization Note** Stated for every global $C^2$-solution of (5) (existence and uniqueness is Theorem 2.1 of the paper). $\liminf_{t\to+\infty}\|x(t)-x^*\|=0$ is written as: for every $\delta>0$, $\|x(t)-x^*\|<\delta$ for arbitrarily large $t$, which avoids the junk value of Lean's `Filter.liminf`. The alternative "in the ball, or in its complement" uses one $T$ for both branches: either $\|x(t)\|<\|x^*\|$ for all $t\ge T$, or $\|x(t)\|\ge\|x^*\|$ for all $t\ge T$. $t^{\alpha/3+1}$ is the real power. Positivity of $\epsilon$ is not assumed; it follows from the hypotheses for $\alpha=3$ and $\alpha>3$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 21, Theorem 4.4

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting

open Set Filter Topology

namespace TikhonovHDD.Strong

/-- Theorem 4.4 (p. 21): `liminf_{t→+∞} ‖x(t) − x⋆‖ = 0` (for every `δ > 0`,
`‖x(t) − x⋆‖ < δ` for arbitrarily large `t`), and `‖x(t) − x⋆‖ → 0` if there is `T ≥ t₀`
such that `{x(t) : t ≥ T}` stays in the open ball `B(0, ‖x⋆‖)` or stays in its complement.
Standing hypotheses (those of Theorem 4.4, arXiv:1911.12845v2, p. 21): the General
assumption, `t₀ > 0`, `α ≥ 3`, `β ≥ 0`, `x` a global `C²`-solution of (5),
`∫_{t₀}^{+∞} ε(t)/t dt < +∞`, `β/(ε(t) t^{α/3+1}) ∫_{t₀}^t ε²(s) s^{α/3+1} ds → 0`,
`ε̇(t) ≤ −(aβ/2) ε²(t)` for `t ≥ t₁` (some `a > 1`, `t₁ ≥ t₀`), for `α = 3`: `t² ε(t) → +∞`,
for `α > 3`: `t² ε(t) ≥ (2/3)α((1/3)α − 1 + βc²)` eventually (some `c > 0`), and `x⋆` the
minimum-norm element of `argmin g`. -/
theorem theorem_4_4
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
    (hxstar : IsMinNormMinimizer g xstar) :
    (∀ δ > (0 : ℝ), ∃ᶠ t in atTop, ‖x t - xstar‖ < δ) ∧
      ((∃ T ≥ t₀, (∀ t ≥ T, ‖x t‖ < ‖xstar‖) ∨ (∀ t ≥ T, ‖xstar‖ ≤ ‖x t‖)) →
        Tendsto (fun t => ‖x t - xstar‖) atTop (𝓝 0)) := by sorry

end TikhonovHDD.Strong
