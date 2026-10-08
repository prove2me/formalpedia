-- Prove2me | Theorems.Thm_TikhonovHDD_Weak_theorem_3_3_i
-- name    : TikhonovHDD.Weak.theorem_3_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:00.829559+00:00
-- url     : https://prove2.me/theorems/3fceb966-d260-4882-9d1f-a37c9a09775b
-- title:
--   Theorem 3.3 (first part) — for $\alpha\ge3$, $g(x(t))-\min g=O(1/t^2)$
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
--   If $\alpha\ge3$, then
--
--   $$g(x(t))-\min g=O\!\left(\frac1{t^2}\right)\qquad (t\to+\infty).$$
--
--   This is the first part of Theorem 3.3: under the strengthened integrability $\int t\epsilon(t)\,dt<+\infty$ the Tikhonov term does not destroy the fast $O(1/t^2)$ rate known for the system without regularization. In the paper it yields $\lim_{t\to+\infty}g(x(t))=\min g$, used in the proof of Theorem 3.5.
--
--   **Formalization Note** The solution $x$ is a map $\mathbb R\to\mathcal H$ with velocity and acceleration maps $\dot x,\ddot x$; derivatives are one-sided (within $[t_0,+\infty)$) at $t_0$, $\ddot x$ is continuous on $[t_0,+\infty)$, and values before $t_0$ are irrelevant. The statement is made for every $C^2$-solution; existence and uniqueness is Theorem 2.1. $\nabla^2 g(x)v$ is the Fréchet derivative of $\nabla g$ at $x$ applied to $v$; $\dot\epsilon$ is a derivative map $\epsilon'$ tied to $\epsilon$ by one-sided derivatives on $[t_0,+\infty)$. $\min g$ is $\inf_{y}g(y)$, attained because $\operatorname{argmin} g\neq\emptyset$. Integrability $\int_{t_0}^{+\infty}|f|<+\infty$ is Lebesgue integrability on $[t_0,+\infty)$ (`IntegrableOn`), and $O$, $o$ are taken as $t\to+\infty$.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 11, Theorem 3.3 (case α ≥ 3)

import Mathlib
import Definitions.Def_TikhonovHDD_Weak_Setting

open Filter Topology Set MeasureTheory Asymptotics

namespace TikhonovHDD.Weak

theorem theorem_3_3_i
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g) (hε : GenAssumptionEps t₀ ε ε')
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    (hint : IntegrableOn (fun t => t * ε t) (Ici t₀))
    (hab : CondA β t₀ ε ε' ∨ CondB t₀ ε)
    (hα : 3 ≤ α) :
    (fun t => g (x t) - minVal g) =O[atTop] (fun t => 1 / t ^ 2) := by sorry

end TikhonovHDD.Weak
