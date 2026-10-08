-- Prove2me | Theorems.Thm_RiemOpt_BFGS_proposition_10
-- name    : RiemOpt.BFGS.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:26:05.035975+00:00
-- url     : https://prove2.me/theorems/718c4f2f-4334-4262-a292-e7b42a69948a
-- title:
--   Proposition 10 — Riemannian BFGS with isometric transports and Wolfe steps converges R-linearly under uniform convexity
-- statement:
--   Let $\mathcal M$ be a Riemannian manifold modelled on a real Hilbert space and consider a non-terminating run of Algorithm 1 with the BFGS search direction and Wolfe step size control (definition **Setting**): $x_{k+1}=R_{x_k}(\alpha_kp_k)$ with $\alpha_k>0$ satisfying (1a)–(1b) for $0<c_1<c_2<1$, $B_k(p_k,\cdot)=-\mathrm Df(x_k)$, and the BFGS update of $B_k$ through transports $T_k:T_{x_k}\mathcal M\to T_{x_{k+1}}\mathcal M$. Assume:
--   1. the $T_k$ are isometries, $\|T_kv\|_{x_{k+1}}=\|v\|_{x_k}$;
--   2. the $f_{R_{x_k}}$ are uniformly convex on the $f(x_0)$-sublevel set of $f$: there are $0<m<M<\infty$ such that, for every $k$, the set $S_k=R_{x_k}^{-1}(\{x:f(x)\le f(x_0)\})$ is convex and
--   $$m\|v\|_{x_k}^2\le\mathrm D^2f_{R_{x_k}}(p)(v,v)\le M\|v\|_{x_k}^2\qquad\forall v\in T_{x_k}\mathcal M,\ p\in S_k;$$
--   3. $B_0$ is symmetric, bounded and coercive;
--   4. $x^*\in\mathcal M$ is a minimizer of $f$, and $x^*\in R_{x_k}(T_{x_k}\mathcal M)$ for every $k$.
--
--   Then there is a constant $0<\mu<1$ such that
--   $$f(x_{k+1})-f(x^*)\le\mu^{k+1}\big(f(x_0)-f(x^*)\big)\qquad\forall k\in\mathbb N.$$
--
--   This is the global R-linear convergence of the BFGS quasi-Newton method on Riemannian manifolds, including infinite-dimensional ones, for any isometric vector transport.
--
--   **Formalization Note** The paper prints $f(x_k)-f(x^*)\le\mu^{k+1}(f(x_0)-f(x^*))$, which at $k=0$ forces $f(x_0)=f(x^*)$ since $\mu<1$; the appendix's own final display bounds $f(x_{k+1})$ (see the milestone on that display). The statement is made for $f(x_{k+1})$, equivalently $f(x_k)-f(x^*)\le\mu^k(f(x_0)-f(x^*))$. $\mu$ is chosen after the run data and before $k$. Reachability of $x^*$ by $R_{x_k}$ is used by the appendix (through $R_{x_k}^{-1}(x^*)$) and is assumed explicitly; convexity of $S_k$ is the reading of "uniformly convex on the sublevel set" that the appendix uses. "Bounded" is automatic for a continuous bilinear form. $f_{R_{x_k}}$ is assumed $C^2$, $f$ differentiable, $\alpha_k>0$, and $\mathrm Df(x_k)\neq0$ for all $k$ (a run that stops is not covered). The existence of $x^*$ is presupposed, not asserted. One retraction family is used for all $k$; geodesic completeness and separability of the manifold are not needed and are dropped.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 608, Proposition 10 (proof: Appendix A, pp. 620–622)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem proposition_10
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hiso : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), ‖T k v‖ = ‖v‖)
    (m Mc : ℝ) (hconv : UniformlyConvexOnSublevel f R x m Mc)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v)
    (xstar : M) (hmin : ∀ y : M, f xstar ≤ f y)
    (hreach : ∀ k, ∃ q : TangentSpace 𝓘(ℝ, E) (x k), R (x k) q = xstar) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧
      ∀ k : ℕ, f (x (k + 1)) - f xstar ≤ μ ^ (k + 1) * (f (x 0) - f xstar) := by sorry

end RiemOpt.BFGS
