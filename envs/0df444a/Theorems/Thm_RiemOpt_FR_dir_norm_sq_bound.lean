-- Prove2me | Theorems.Thm_RiemOpt_FR_dir_norm_sq_bound
-- name    : RiemOpt.FR.dir_norm_sq_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:51.867825+00:00
-- url     : https://prove2.me/theorems/1fde545d-1513-449b-88cd-21181edf37a2
-- title:
--   Proof of Proposition 15, p. 611 — ‖p_k‖² ≤ (1+c₂)/(1−c₂)·‖Df(x_k)‖⁴·Σ_{j=0}^k ‖Df(x_j)‖⁻² under non-expansive transport
-- statement:
--   Consider a non-terminating Riemannian Fletcher–Reeves run as in Lemma 14 (strong Wolfe steps with $0<c_1<c_2<\tfrac12$, $\alpha_k>0$, $x_{k+1}=R_{x_k}(\alpha_kp_k)$, $p_0=-\nabla f(x_0)$, $p_{k+1}=-\nabla f(x_{k+1})+\beta_{k+1}T^{R_{x_k}}_{x_k,x_{k+1}}p_k$ with $\beta_{k+1}=\|\mathrm Df(x_{k+1})\|^2/\|\mathrm Df(x_k)\|^2$), and suppose the transport does not increase the norm of the search direction:
--   $$\bigl\|T^{R_{x_k}}_{x_k,x_{k+1}}p_k\bigr\|_{x_{k+1}}\le\|p_k\|_{x_k}\qquad\forall k\in\mathbb N.$$
--   Then for every $k\in\mathbb N$
--   $$\|p_k\|_{x_k}^2\ \le\ \frac{1+c_2}{1-c_2}\,\|\mathrm Df(x_k)\|_{x_k}^4\sum_{j=0}^{k}\|\mathrm Df(x_j)\|_{x_j}^{-2}.$$
--
--   The bound shows that the search directions can grow at most linearly in $k$ (relative to the gradient) as long as the gradient norms stay bounded away from zero; combined with the summability of $\|\mathrm Df(x_k)\|^4/\|p_k\|^2$ it yields Proposition 15.
--
--   **Formalization Note** No lower bound on $f$ and no Lipschitz hypothesis are needed. The norm on the left of the transport hypothesis is that of $T_{x_{k+1}}\mathcal M$; the transported vector lives in $T_{R_{x_k}(\alpha_kp_k)}\mathcal M$, which equals $T_{x_{k+1}}\mathcal M$ by the step equation. $\|\mathrm Df(x_j)\|^{-2}$ is written $(\|\mathrm Df(x_j)\|^2)^{-1}$; it is nondegenerate because the run never stops.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 611, proof of Proposition 15

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem dir_norm_sq_bound
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hT : ∀ k : ℕ, ‖transportedDir R x p α k‖ ≤ ‖p k‖) :
    ∀ k : ℕ, ‖p k‖ ^ 2 ≤ (1 + c₂) / (1 - c₂) * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 4 *
      ∑ j ∈ Finset.range (k + 1), (‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2)⁻¹ := by sorry

end RiemOpt.FR
