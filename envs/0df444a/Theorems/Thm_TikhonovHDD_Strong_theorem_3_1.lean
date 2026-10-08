-- Prove2me | Theorems.Thm_TikhonovHDD_Strong_theorem_3_1
-- name    : TikhonovHDD.Strong.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:48.787349+00:00
-- url     : https://prove2.me/theorems/a83e1e74-c68a-4162-94fc-77ae1d8762bd
-- title:
--   Theorem 3.1 — $g(x(t))\to\min g$ under condition (a) or (b) on the Tikhonov parameter, for $\alpha\ge 3$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha\ge 3$, $\beta\ge 0$, $u_0,v_0\in\mathcal H$, and let $g$ and $\epsilon$ satisfy the General assumption: $g$ convex, twice Fréchet differentiable, with gradient Lipschitz continuous on bounded sets and $\operatorname{argmin} g\neq\emptyset$; $\epsilon:[t_0,+\infty)\to[0,+\infty)$ nonincreasing, of class $C^1$, with $\epsilon(t)\to0$. Let $x$ be a global $C^2$-solution of
--   $$
--   \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0 .
--   $$
--   Assume that one of the following conditions holds:
--
--   1. (a) $\int_{t_0}^{+\infty}\frac{\epsilon(t)}{t}\,dt<+\infty$, and there exist $a>1$ and $t_1\ge t_0$ such that $\dot\epsilon(t)\le-\frac{a\beta}{2}\epsilon^2(t)$ for every $t\ge t_1$;
--   2. (b) there exist $a>0$ and $t_1\ge t_0$ such that $\epsilon(t)\le\frac{a}{t}$ for every $t\ge t_1$.
--
--   Then
--   $$
--   \lim_{t\to+\infty}g(x(t))=\min g .
--   $$
--
--   The theorem says that the objective values along the trajectory are minimizing as soon as the Tikhonov parameter either decays slowly in the sense of (a) or at least as fast as $1/t$. In the proof of Theorem 4.4 it supplies $g(x(t))\to\min g$ in the case where the trajectory eventually stays inside the ball $B(0,\|x^*\|)$.
--
--   **Formalization Note** The theorem is stated for every global $C^2$-solution of (5); existence and uniqueness of that solution is Theorem 2.1 of the paper. Finiteness of $\int_{t_0}^{+\infty}\epsilon(t)/t\,dt$ is integrability of $t\mapsto\epsilon(t)/t$ on $[t_0,+\infty)$. $\min g$ is the infimum of the range of $g$, attained because $\operatorname{argmin} g\neq\emptyset$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, pp. 5–6, Theorem 3.1

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting

open Set Filter Topology

namespace TikhonovHDD.Strong

/-- Theorem 3.1 (arXiv:1911.12845v2, pp. 5–6). Under the General assumption, let `x` be a
global `C²`-solution of (5) with `t₀ > 0`, `α ≥ 3`, `β ≥ 0`. If either
(a) `∫_{t₀}^{+∞} ε(t)/t dt < +∞` and `ε̇(t) ≤ −(aβ/2) ε²(t)` for all `t ≥ t₁`, for some `a > 1`,
`t₁ ≥ t₀`; or
(b) `ε(t) ≤ a/t` for all `t ≥ t₁`, for some `a > 0`, `t₁ ≥ t₀`,
then `g(x(t)) → min g` as `t → +∞`. -/
theorem theorem_3_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd)
    (hcond :
      (MeasureTheory.IntegrableOn (fun t => ε t / t) (Ici t₀) ∧
        ∃ a > (1 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε' t ≤ -(a * β / 2) * ε t ^ 2) ∨
      (∃ a > (0 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε t ≤ a / t)) :
    Tendsto (fun t => g (x t)) atTop (𝓝 (minValue g)) := by sorry

end TikhonovHDD.Strong
