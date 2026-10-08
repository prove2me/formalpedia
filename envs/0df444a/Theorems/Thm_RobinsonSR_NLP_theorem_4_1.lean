-- Prove2me | Theorems.Thm_RobinsonSR_NLP_theorem_4_1
-- name    : RobinsonSR.NLP.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:26.88977+00:00
-- url     : https://prove2.me/theorems/771aa74c-64f6-49f2-a341-f85e209b808e
-- title:
--   Theorem 4.1, p. 56 — strong second-order sufficiency and independent binding gradients make the KKT system (4.3) strongly regular
-- statement:
--   Consider the nonlinear program
--   $$\text{minimize } \theta(x)\quad\text{subject to } g(x)\le0,\ h(x)=0,\qquad(4.1)$$
--   where $\theta,g,h$ are defined on an open set $\Omega\subseteq\mathbb R^n$ with values in $\mathbb R$, $\mathbb R^p$, $\mathbb R^q$, are Fréchet differentiable on $\Omega$, and are twice differentiable at a point $x_0\in\Omega$. Let $u_0\in\mathbb R^p$ and $v_0\in\mathbb R^q$ be such that $(x_0,u_0,v_0)$ solves the KKT generalized equation
--   $$0\in\begin{bmatrix}\mathcal L'(x,u,v)\\-g(x)\\-h(x)\end{bmatrix}+\partial\psi_{\mathbb R^n\times\mathbb R^p_+\times\mathbb R^q}\begin{bmatrix}x\\u\\v\end{bmatrix},\qquad(4.3)$$
--   with $\mathcal L(x,u,v)=\theta(x)+\langle u,g(x)\rangle+\langle v,h(x)\rangle$. Write $\mathcal L''=\mathcal L''(x_0,u_0,v_0)$ for the Hessian in $x$. Assume
--   1. **(a′) strong second-order sufficiency:** $\langle y,\mathcal L''y\rangle>0$ for every nonzero $y$ with $\langle\nabla g_i(x_0),y\rangle=0$ whenever $u_{0,i}>0$ and $\langle\nabla h_j(x_0),y\rangle=0$ for all $j$;
--   2. **(b) linear independence:** the gradients $\nabla g_i(x_0)$ of the binding inequality constraints ($g_i(x_0)=0$) together with all $\nabla h_j(x_0)$ are linearly independent.
--
--   Then (4.3) is strongly regular at $(x_0,u_0,v_0)$: for some $\lambda$, the linearisation of (4.3) at $(x_0,u_0,v_0)$ has, for all perturbations in a neighbourhood of $0$, a unique solution near $(x_0,u_0,v_0)$, depending $\lambda$-Lipschitz-continuously on the perturbation.
--
--   The theorem does not assume strict complementary slackness: weakly active constraints ($g_i(x_0)=0=u_{0,i}$) are allowed, and (a′) is imposed only on the directions annihilated by the gradients of constraints with positive multipliers.
--
--   **Formalization Note** "Differentiable on $\Omega$" is the standing assumption of (4.1); "twice differentiable at $x_0$" is encoded as differentiability at $x_0$ of each gradient $\nabla\theta$, $\nabla g_i$, $\nabla h_j$. Symmetry of $\mathcal L''$ is not assumed; it follows from these hypotheses. Triples $(x,u,v)$ carry the Euclidean norm of $\mathbb R^{n+p+q}$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 56, Theorem 4.1; conditions (a′) and (b) p. 55; (4.1)–(4.3) pp. 53–54

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Theorem 4.1, p. 56: let `θ, g, h` be functions from an open set `Ω ⊆ ℝⁿ` to `ℝ, ℝᵖ, ℝ^q`,
differentiable on `Ω` (the standing assumption of (4.1)) and twice differentiable at `x₀ ∈ Ω`.
Suppose `(x₀, u₀, v₀)` solves (4.3). If the strong second-order sufficient condition (a′) holds
at `(x₀, u₀, v₀)` together with linear independence (b) of the gradients of the binding
constraints, then (4.3) is strongly regular there. -/
theorem theorem_4_1 {n p q : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hθ : DifferentiableOn ℝ θ Ω)
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hsol : -(kktMap θ g h (mk x0 u0 v0)) ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) (mk x0 u0 v0))
    (hSSOSC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      (∀ i, 0 < u0 i → ⟪gradient (fun x => g x i) x0, y⟫ = 0) →
      (∀ j, ⟪gradient (fun x => h x j) x0, y⟫ = 0) →
      0 < ⟪y, lagHess θ g h x0 u0 v0 y⟫)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i : {i : Fin p // g x0 i = 0} => gradient (fun x => g x i) x0)
        (fun j : Fin q => gradient (fun x => h x j) x0))) :
    StronglyRegularAt (kktMap θ g h) (kktCone n p q) (mk x0 u0 v0) := by sorry

end RobinsonSR.NLP
