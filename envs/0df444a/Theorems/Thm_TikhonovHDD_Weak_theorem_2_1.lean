-- Prove2me | Theorems.Thm_TikhonovHDD_Weak_theorem_2_1
-- name    : TikhonovHDD.Weak.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:59.128331+00:00
-- url     : https://prove2.me/theorems/915a7b43-de18-4631-98da-effde5ddd276
-- title:
--   Theorem 2.1 — existence and uniqueness of a global $C^2$-solution of (5) (with $g\in C^2$ when $\beta>0$)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha\ge3$, $\beta\ge0$, and let $g$ and $\epsilon$ satisfy the General assumption: $g:\mathcal H\to\mathbb R$ convex, twice Fréchet differentiable, with $\nabla g$ Lipschitz continuous on bounded sets and $\operatorname{argmin} g\ne\emptyset$; $\epsilon:[t_0,+\infty)\to[0,+\infty)$ nonincreasing, $C^1$, with $\epsilon(t)\to0$. Assume moreover that $\beta=0$ or $g$ is of class $C^2$. Then for every initial value $(u_0,v_0)\in\mathcal H\times\mathcal H$ there exists a unique global $C^2$-solution $x:[t_0,+\infty)\to\mathcal H$ of
--
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad x(t_0)=u_0,\ \dot x(t_0)=v_0.$$
--
--   Uniqueness means that any two global $C^2$-solutions coincide on $[t_0,+\infty)$. This well-posedness result is what makes "the unique global $C^2$-solution of (5)" in every later statement meaningful.
--
--   **Formalization Note** The hypothesis "$\beta=0$ or $g\in C^2$" is a repair. The paper assumes only that $g$ is twice Fréchet differentiable, and its proof (p. 5) uses that $\nabla g$ is continuously differentiable. For $\beta>0$ the printed statement fails: on $\mathcal H=\mathbb R$ take $g'(x)=2x+x^2\sin(1/x)$, $g'(0)=0$; then $g''(x)=2+2x\sin(1/x)-\cos(1/x)\ge1-2/\pi>0$ is bounded but discontinuous at $0$, and with $u_0=0$, $v_0=1$ the acceleration $\ddot x(t)$ of the unique solution contains $-\beta g''(x(t))\dot x(t)$, which oscillates as $t\downarrow t_0$, so no $C^2$-solution exists. For $\beta=0$ the printed hypotheses suffice and are kept. Derivatives at $t_0$ are one-sided, values before $t_0$ are irrelevant, and $\nabla^2g(x)v$ is the derivative of $\nabla g$ at $x$ applied to $v$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 4, Theorem 2.1 (proof pp. 4–5)

import Mathlib
import Definitions.Def_TikhonovHDD_Weak_Setting

open Filter Topology Set MeasureTheory Asymptotics

namespace TikhonovHDD.Weak

theorem theorem_2_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hg : GenAssumptionG g) (hε : GenAssumptionEps t₀ ε ε')
    (hC2 : β = 0 ∨ ContDiff ℝ 2 g) (u₀ v₀ : H) :
    (∃ x xd xdd : ℝ → H, IsSolution g ε α β t₀ u₀ v₀ x xd xdd) ∧
    (∀ x xd xdd y yd ydd : ℝ → H,
      IsSolution g ε α β t₀ u₀ v₀ x xd xdd → IsSolution g ε α β t₀ u₀ v₀ y yd ydd →
      ∀ t ∈ Ici t₀, x t = y t) := by sorry

end TikhonovHDD.Weak
