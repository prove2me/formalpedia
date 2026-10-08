-- Prove2me | Theorems.Thm_RiemOpt_FR_cos_theta_bounds
-- name    : RiemOpt.FR.cos_theta_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:52.350128+00:00
-- url     : https://prove2.me/theorems/d26e3990-f192-47cd-9351-4e09b5a7252f
-- title:
--   Proof of Proposition 15, p. 611 — (1−2c₂)/(1−c₂)·‖Df(x_k)‖/‖p_k‖ ≤ cos θ_k ≤ 1/(1−c₂)·‖Df(x_k)‖/‖p_k‖
-- statement:
--   Under the hypotheses of Lemma 14 — a non-terminating Riemannian Fletcher–Reeves run $x_{k+1}=R_{x_k}(\alpha_kp_k)$, $\alpha_k>0$, with strong Wolfe steps (1a), (2) for $0<c_1<c_2<\tfrac12$, $p_0=-\nabla f(x_0)$ and $p_{k+1}=-\nabla f(x_{k+1})+\beta_{k+1}T^{R_{x_k}}_{x_k,x_{k+1}}p_k$ — the angle $\theta_k$ between $p_k$ and $-\nabla f(x_k)$, defined by $\cos\theta_k=-\mathrm Df(x_k)p_k/(\|\mathrm Df(x_k)\|_{x_k}\|p_k\|_{x_k})$, satisfies for every $k\in\mathbb N$
--   $$\frac{1-2c_2}{1-c_2}\,\frac{\|\mathrm Df(x_k)\|_{x_k}}{\|p_k\|_{x_k}}\ \le\ \cos\theta_k\ \le\ \frac{1}{1-c_2}\,\frac{\|\mathrm Df(x_k)\|_{x_k}}{\|p_k\|_{x_k}}.$$
--
--   This is the first step of the proof of Proposition 15: it turns Zoutendijk's theorem into a summability statement about $\|\mathrm Df(x_k)\|^4/\|p_k\|^2$.
--
--   **Formalization Note** Same run conventions as Lemma 14 (no descent assumption, $\mathrm Df(x_k)\neq0$, one retraction family, indices from $0$). The quotients are not degenerate: Lemma 14 forces $\mathrm Df(x_k)p_k<0$, hence $p_k\neq0$.
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

theorem cos_theta_bounds
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2) :
    ∀ k : ℕ, (1 - 2 * c₂) / (1 - c₂) * (‖RiemOpt.BFGS.Df (E := E) f (x k)‖ / ‖p k‖) ≤ cosTheta f x p k ∧
      cosTheta f x p k ≤ 1 / (1 - c₂) * (‖RiemOpt.BFGS.Df (E := E) f (x k)‖ / ‖p k‖) := by sorry

end RiemOpt.FR
