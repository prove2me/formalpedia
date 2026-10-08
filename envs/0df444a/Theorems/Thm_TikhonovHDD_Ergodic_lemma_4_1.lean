-- Prove2me | Theorems.Thm_TikhonovHDD_Ergodic_lemma_4_1
-- name    : TikhonovHDD.Ergodic.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:12.808556+00:00
-- url     : https://prove2.me/theorems/cb0cc9c4-35cb-40bf-854e-678f561da2e0
-- title:
--   Lemma 4.1 — bounded velocity, ‖ẋ(t)‖²/t ∈ L¹, and sup (1/t)|ḣ_{x*}(t)| < +∞
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, and let $g$ and $\epsilon$ satisfy the General assumption: $g$ convex, twice Fréchet differentiable, with gradient Lipschitz on bounded sets and $\operatorname{argmin} g\ne\emptyset$; $\epsilon:[t_0,+\infty)\to[0,+\infty)$ nonincreasing, $C^1$, with $\epsilon(t)\to0$. Let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   If $\alpha>0$ and $\beta\ge0$, then
--   $$
--   \sup_{t\ge t_0}\|\dot x(t)\|<+\infty\qquad\text{and}\qquad \frac1t\|\dot x(t)\|^2\in L^1([t_0,+\infty),\mathbb R).
--   $$
--   In addition, for every $x^*\in\operatorname{argmin} g$, with $h_{x^*}(t)=\tfrac12\|x(t)-x^*\|^2$,
--   $$
--   \sup_{t\ge t_0}\frac1t\,|\dot h_{x^*}(t)|<+\infty .
--   $$
--
--   These estimates hold for every $\alpha>0$, below the threshold $\alpha\ge3$ used elsewhere in the paper, and they bound the right-hand side of the integrated inequality in the proof of Theorem 4.2.
--
--   **Formalization Note** "$\sup<+\infty$" is stated as boundedness from above of the image of $[t_0,+\infty)$. $L^1$ membership is integrability on $[t_0,+\infty)$ with respect to Lebesgue measure. $\dot h_{x^*}(t)$ is $\langle\dot x(t),x(t)-x^*\rangle$, the derivative of $h_{x^*}$. The point $x^*$ is any minimizer of $g$, as in the paper. The statement is made for every global $C^2$-solution; existence (and uniqueness) of the solution is Theorem 2.1 of the paper.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 16, Lemma 4.1

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting

open Set Filter Topology MeasureTheory

namespace TikhonovHDD.Ergodic

/-- Lemma 4.1 (p. 16): if `α > 0` and `β ≥ 0`, every global `C²`-solution of (5) has bounded
velocity, `t ↦ ‖ẋ(t)‖²/t` is integrable on `[t₀, +∞)`, and for every `x⋆ ∈ argmin g` the
function `t ↦ |ḣ_{x⋆}(t)|/t` is bounded on `[t₀, +∞)`. -/
theorem lemma_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd) :
    BddAbove ((fun t => ‖xd t‖) '' Ici t₀) ∧
      IntegrableOn (fun t => ‖xd t‖ ^ 2 / t) (Ici t₀) ∧
      ∀ xstar ∈ TikhonovHDD.Strong.argminSet g, BddAbove ((fun t => |hDot x xd xstar t| / t) '' Ici t₀) := by sorry

end TikhonovHDD.Ergodic
