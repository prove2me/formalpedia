-- Prove2me | Theorems.Thm_TikhonovHDD_Weak_theorem_3_3_ii
-- name    : TikhonovHDD.Weak.theorem_3_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:09.600114+00:00
-- url     : https://prove2.me/theorems/df3684ed-1c19-444a-bb16-4373f386524d
-- title:
--   Theorem 3.3 (second part) — for $\alpha>3$, $x$ is bounded and $t(g(x)-\min g)$, $t\|\dot x\|^2$, $t\epsilon\|x-x^*\|^2$, $t\epsilon\|x\|^2\in L^1$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $t_0>0$, $\alpha\in\mathbb R$, $\beta\ge 0$ and $u_0,v_0\in\mathcal H$. Let $g:\mathcal H\to\mathbb R$ be convex and twice Fréchet differentiable, with gradient $\nabla g$ Lipschitz continuous on bounded sets and $\operatorname{argmin} g\neq\emptyset$, and let $\epsilon:[t_0,+\infty)\to[0,+\infty)$ be nonincreasing, of class $C^1$, with $\lim_{t\to+\infty}\epsilon(t)=0$ (the General assumption). Let $x:[t_0,+\infty)\to\mathcal H$ be a global $C^2$-solution of
--
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta\nabla^2 g(x(t))\dot x(t)+\nabla g(x(t))+\epsilon(t)x(t)=0,\qquad t\ge t_0,\quad x(t_0)=u_0,\ \dot x(t_0)=v_0. \tag{5}$$
--
--   Assume that $\int_{t_0}^{+\infty} t\epsilon(t)\,dt<+\infty$ and that one of the following conditions holds:
--
--   1. (a) there exist $a>1$ and $t_1\ge t_0$ such that $\dot\epsilon(t)\le-\frac{a\beta}{2}\epsilon^2(t)$ for every $t\ge t_1$;
--   2. (b) there exist $a>0$ and $t_1\ge t_0$ such that $\epsilon(t)\le\frac{a}{t}$ for every $t\ge t_1$.
--
--   Write $\min g$ for the minimal value of $g$.
--
--   If $\alpha>3$, then the trajectory $x$ is bounded on $[t_0,+\infty)$ and, for every $x^*\in\operatorname{argmin} g$,
--
--   $$t\bigl(g(x(t))-\min g\bigr),\quad t\|\dot x(t)\|^2,\quad t\epsilon(t)\|x(t)-x^*\|^2,\quad t\epsilon(t)\|x(t)\|^2\ \in L^1([t_0,+\infty),\mathbb R).$$
--
--   This is the second part of Theorem 3.3 without its last integrability claim, which is stated separately (Theorem 3.3, gradient part). These integrability estimates feed the proof of Theorem 3.4.
--
--   **Formalization Note** The solution $x$ is a map $\mathbb R\to\mathcal H$ with velocity and acceleration maps $\dot x,\ddot x$; derivatives are one-sided (within $[t_0,+\infty)$) at $t_0$, $\ddot x$ is continuous on $[t_0,+\infty)$, and values before $t_0$ are irrelevant. The statement is made for every $C^2$-solution; existence and uniqueness is Theorem 2.1. $\nabla^2 g(x)v$ is the Fréchet derivative of $\nabla g$ at $x$ applied to $v$; $\dot\epsilon$ is a derivative map $\epsilon'$ tied to $\epsilon$ by one-sided derivatives on $[t_0,+\infty)$. $\min g$ is $\inf_{y}g(y)$, attained because $\operatorname{argmin} g\neq\emptyset$. Integrability $\int_{t_0}^{+\infty}|f|<+\infty$ is Lebesgue integrability on $[t_0,+\infty)$ (`IntegrableOn`), and $O$, $o$ are taken as $t\to+\infty$. Boundedness is $\sup_{t\ge t_0}\|x(t)\|<+\infty$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 11, Theorem 3.3 (case α > 3: boundedness and the first four integrability claims)

import Mathlib
import Definitions.Def_TikhonovHDD_Weak_Setting

open Filter Topology Set MeasureTheory Asymptotics

namespace TikhonovHDD.Weak

theorem theorem_3_3_ii
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g) (hε : GenAssumptionEps t₀ ε ε')
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    (hint : IntegrableOn (fun t => t * ε t) (Ici t₀))
    (hab : CondA β t₀ ε ε' ∨ CondB t₀ ε)
    (hα : 3 < α) :
    (∃ C : ℝ, ∀ t ∈ Ici t₀, ‖x t‖ ≤ C) ∧
    ∀ xs ∈ argmin g,
      IntegrableOn (fun t => t * (g (x t) - minVal g)) (Ici t₀) ∧
      IntegrableOn (fun t => t * ‖xd t‖ ^ 2) (Ici t₀) ∧
      IntegrableOn (fun t => t * ε t * ‖x t - xs‖ ^ 2) (Ici t₀) ∧
      IntegrableOn (fun t => t * ε t * ‖x t‖ ^ 2) (Ici t₀) := by sorry

end TikhonovHDD.Weak
