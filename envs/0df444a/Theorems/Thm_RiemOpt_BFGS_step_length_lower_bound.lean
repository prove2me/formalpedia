-- Prove2me | Theorems.Thm_RiemOpt_BFGS_step_length_lower_bound
-- name    : RiemOpt.BFGS.step_length_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:45.514317+00:00
-- url     : https://prove2.me/theorems/4a44a1bc-fa51-4e7f-a99a-330c865b2b06
-- title:
--   Appendix A, proof of Proposition 10, p. 622 — α_i ≥ −Df(x_i)p_i/‖p_i‖² · (1 − c₂)/M = (1 − c₂)/M · q_i
-- statement:
--   Consider a non-terminating Riemannian BFGS run with Wolfe steps (definition **Setting**) in which the transports $T_k$ are isometries, $B_0$ is symmetric and coercive, and the $f_{R_{x_k}}$ are uniformly convex on the $f(x_0)$-sublevel set with constants $0<m<M$. Then for every index $i$
--   $$\alpha_i\ \ge\ -\frac{\mathrm Df(x_i)p_i}{\|p_i\|_{x_i}^2}\cdot\frac{1-c_2}{M}\qquad\text{and}\qquad -\frac{\mathrm Df(x_i)p_i}{\|p_i\|_{x_i}^2}=q_i,$$
--   so that $\alpha_i\ge\frac{1-c_2}{M}q_i$, with $q_i=B_i(s_i,s_i)/\|s_i\|_{x_i}^2$ the Rayleigh quotient.
--
--   The curvature condition (1b) together with the upper Hessian bound forbids too short steps; this lower bound on $\alpha_i$ is what turns the sufficient-decrease condition (1a) into a fixed fraction of decrease at the good indices.
--
--   **Formalization Note** Only the part of the display up to "$=\frac{1-c_2}{M}q_i$" is stated; the final "$\ge\frac{1-c_2}{M}\kappa\rho$" is the specialization to good indices. The statement holds at every index $i$ of the run.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 622, Appendix A, proof of Proposition 10

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem step_length_lower_bound
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hiso : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), ‖T k v‖ = ‖v‖)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v)
    (m Mc : ℝ) (hconv : UniformlyConvexOnSublevel f R x m Mc) :
    ∀ i, (1 - c₂) / Mc * (-(Df f (x i) (p i)) / ‖p i‖ ^ 2) ≤ α i ∧
      -(Df f (x i) (p i)) / ‖p i‖ ^ 2 = rayleighQ x p α B i := by sorry

end RiemOpt.BFGS
