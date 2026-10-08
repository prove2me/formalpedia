-- Prove2me | Theorems.Thm_RiemOpt_FR_proposition_15
-- name    : RiemOpt.FR.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:17.963066+00:00
-- url     : https://prove2.me/theorems/8ca49aa5-7dc6-4583-982e-25379d60123a
-- title:
--   Proposition 15 — Riemannian Fletcher–Reeves CG with strong Wolfe steps, c₂ < 1/2, non-expansive transport: liminf ‖Df(x_k)‖ = 0
-- statement:
--   Let $\mathcal M$ be a smooth manifold modelled on a real Hilbert space with a Riemannian metric, $f:\mathcal M\to\mathbb R$ differentiable with gradient $\nabla f$, and $R$ a retraction family with transport $T^{R_x}_{x,R_x(v)}=\mathrm DR_x(v)$. Consider the Fletcher–Reeves nonlinear conjugate gradient iteration
--   $$x_{k+1}=R_{x_k}(\alpha_kp_k),\qquad p_0=-\nabla f(x_0),\qquad p_{k+1}=-\nabla f(x_{k+1})+\frac{\|\mathrm Df(x_{k+1})\|_{x_{k+1}}^2}{\|\mathrm Df(x_k)\|_{x_k}^2}\,T^{R_{x_k}}_{x_k,x_{k+1}}p_k,$$
--   with step lengths $\alpha_k>0$ satisfying the strong Wolfe conditions (1a), (2) with $0<c_1<c_2<\tfrac12$, and assume that it never stops ($\mathrm Df(x_k)\neq0$ for all $k$). Suppose that
--
--   1. the transport does not increase the norm of the search direction: $\|T^{R_{x_k}}_{x_k,x_{k+1}}p_k\|_{x_{k+1}}\le\|p_k\|_{x_k}$ for all $k$;
--   2. $f$ is bounded below;
--   3. the pull-backs $f\circ R_{x_k}$ are Lipschitz continuously differentiable on $\mathrm{span}\{p_k\}$ with a uniform constant $L>0$: $h_k(t)=f(R_{x_k}(tp_k))$ is differentiable and $|h_k'(s)-h_k'(t)|\le L|s-t|\,\|p_k\|_{x_k}^2$.
--
--   Then
--   $$\liminf_{k\to\infty}\|\mathrm Df(x_k)\|_{x_k}=0.$$
--
--   This is the Riemannian counterpart of the classical global convergence result of Al-Baali for the Fletcher–Reeves method: on a manifold the only extra ingredient is the non-expansiveness of the transport attached to the retraction.
--
--   **Formalization Note** Hypotheses 2 and 3 are those of Zoutendijk's theorem (Theorem 2), which the paper's proof invokes; they are not among the conditions of Lemma 14 and are stated explicitly. Descent of $p_k$ is not assumed (Lemma 14 proves it). The run never stops, since $\beta_{k+1}$ divides by $\|\mathrm Df(x_k)\|^2$. The $\liminf$ is stated explicitly: for every $\varepsilon>0$ and every $N$ there is $k\ge N$ with $\|\mathrm Df(x_k)\|_{x_k}<\varepsilon$. One retraction family is used for all $k$; the step equation identifies $T_{R_{x_k}(\alpha_kp_k)}\mathcal M$ with $T_{x_{k+1}}\mathcal M$, whose norm is used in hypothesis 1.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 611, Proposition 15

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem proposition_15
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hT : ∀ k : ℕ, ‖transportedDir R x p α k‖ ≤ ‖p k‖)
    (hbdd : BddBelow (Set.range f)) (L : ℝ) (hL : 0 < L) (hlip : LineLipschitz f R x p L) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ < ε := by sorry

end RiemOpt.FR
