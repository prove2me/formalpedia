-- Prove2me | Theorems.Thm_RiemOpt_BFGS_curvature_pair_bounds
-- name    : RiemOpt.BFGS.curvature_pair_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:42.407499+00:00
-- url     : https://prove2.me/theorems/aafeb035-3bf2-4ab7-a367-b7b5cfdcc080
-- title:
--   Appendix A, proof of Proposition 10, p. 620 — $\|y_k\|^2/(y_ks_k)\le M$ and $y_ks_k/\|s_k\|^2\ge m$
-- statement:
--   Consider a non-terminating Riemannian BFGS run with Wolfe steps (definition **Setting**) in which the transports $T_k$ are isometries, $B_0$ is symmetric and coercive, and the pulled-back objectives $f_{R_{x_k}}$ are uniformly convex on the $f(x_0)$-sublevel set with constants $0<m<M$: the sets $S_k=R_{x_k}^{-1}(\{f\le f(x_0)\})$ are convex and $m\|v\|^2_{x_k}\le\mathrm D^2f_{R_{x_k}}(p)(v,v)\le M\|v\|^2_{x_k}$ for $p\in S_k$. Then for every $k$
--   $$\frac{\|y_k\|_{x_k}^2}{y_ks_k}\le M,\qquad \frac{y_ks_k}{\|s_k\|_{x_k}^2}\ge m,$$
--   where $\|y_k\|_{x_k}$ is the dual norm of the functional $y_k$.
--
--   These two bounds on the curvature pair $(s_k,y_k)$ feed the trace estimate in the convergence proof of Proposition 10.
--
--   **Formalization Note** The paper derives the bounds from the averaged Hessian $G_k=\int_0^1\mathrm D^2f_{R_{x_k}}(ts_k)\,\mathrm dt$; only the resulting inequalities are stated. The hypotheses are those of Proposition 10 except the minimizer $x^*$; isometry and the conditions on $B_0$ are what guarantee, through Lemma 9, that the iterates stay in the sublevel set so that the segment $[0,s_k]$ lies in $S_k$. $s_k\neq0$ along such a run, so neither quotient is a division by zero.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 620, Appendix A, proof of Proposition 10

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem curvature_pair_bounds
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hiso : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), ‖T k v‖ = ‖v‖)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v)
    (m Mc : ℝ) (hconv : UniformlyConvexOnSublevel f R x m Mc) :
    ∀ k, ‖yVec f R x p α k‖ ^ 2 / yVec f R x p α k (sVec x p α k) ≤ Mc ∧
      m ≤ yVec f R x p α k (sVec x p α k) / ‖sVec x p α k‖ ^ 2 := by sorry

end RiemOpt.BFGS
