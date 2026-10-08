-- Prove2me | Theorems.Thm_RiemOpt_FR_lemma_14
-- name    : RiemOpt.FR.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:01.481021+00:00
-- url     : https://prove2.me/theorems/62eb27a0-21b6-4dd4-90ff-d8116aef3e69
-- title:
--   Lemma 14 — Riemannian Fletcher–Reeves with strong Wolfe steps, c₂ < 1/2: −1/(1−c₂) ≤ Df(x_k)p_k/‖Df(x_k)‖² ≤ (2c₂−1)/(1−c₂)
-- statement:
--   Let $\mathcal M$ be a smooth Riemannian manifold modelled on a real Hilbert space, $f:\mathcal M\to\mathbb R$ differentiable with gradient $\nabla f$, and $R$ a retraction family with transport $T^{R_x}_{x,R_x(v)}=\mathrm DR_x(v)$. Consider a non-terminating Fletcher–Reeves run: $x_{k+1}=R_{x_k}(\alpha_kp_k)$ with $\alpha_k>0$ satisfying the strong Wolfe conditions (1a), (2) with $0<c_1<c_2<\tfrac12$, $p_0=-\nabla f(x_0)$,
--   $$p_{k+1}=-\nabla f(x_{k+1})+\beta_{k+1}T^{R_{x_k}}_{x_k,x_{k+1}}p_k,\qquad \beta_{k+1}=\frac{\|\mathrm Df(x_{k+1})\|_{x_{k+1}}^2}{\|\mathrm Df(x_k)\|_{x_k}^2},$$
--   and $\mathrm Df(x_k)\neq0$ for all $k$. Then for every $k\in\mathbb N$,
--   $$-\frac{1}{1-c_2}\ \le\ \frac{\mathrm Df(x_k)p_k}{\|\mathrm Df(x_k)\|_{x_k}^2}\ \le\ \frac{2c_2-1}{1-c_2}.$$
--
--   Since $c_2<\tfrac12$, the upper bound is negative, so every Fletcher–Reeves direction is a descent direction; the two bounds also control the angle between $p_k$ and $-\nabla f(x_k)$ in terms of $\|\mathrm Df(x_k)\|/\|p_k\|$.
--
--   **Formalization Note** That $p_k$ is a descent direction is *not* assumed: it is a consequence of the lemma. The algorithm is assumed not to stop ($\mathrm Df(x_k)\ne0$), since $\beta_{k+1}$ divides by $\|\mathrm Df(x_k)\|^2$. One retraction family is used for all $k$; the step equation $x_{k+1}=R_{x_k}(\alpha_kp_k)$ is what lets the transported direction be used in $T_{x_{k+1}}\mathcal M$. Indices start at $0$.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 610, Lemma 14

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem lemma_14
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2) :
    ∀ k : ℕ, -1 / (1 - c₂) ≤ RiemOpt.BFGS.Df (E := E) f (x k) (p k) / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 ∧
      RiemOpt.BFGS.Df (E := E) f (x k) (p k) / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 ≤ (2 * c₂ - 1) / (1 - c₂) := by sorry

end RiemOpt.FR
