-- Prove2me | Theorems.Thm_RiemOpt_BFGS_rate_display
-- name    : RiemOpt.BFGS.rate_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:05.232149+00:00
-- url     : https://prove2.me/theorems/a4448478-4e7d-457b-9b8d-edcb5f5f134c
-- title:
--   Appendix A, proof of Proposition 10, p. 622 — f(x_{k+1}) − f(x*) ≤ (1 − (1−c₂)/M c₁ κ²ρ/σ 2m)^⌊r(k+1)⌋ (f(x₀) − f(x*))
-- statement:
--   Consider a non-terminating Riemannian BFGS run with Wolfe steps (definition **Setting**) in which the transports $T_k$ are isometries, $B_0$ is symmetric and coercive, the $f_{R_{x_k}}$ are uniformly convex on the $f(x_0)$-sublevel set with constants $0<m<M$, and $x^*$ is a global minimizer of $f$ reachable from every iterate, $x^*\in R_{x_k}(T_{x_k}\mathcal M)$. Let $0<r<1$ and $\kappa,\rho,\sigma>0$ be such that for every $k$ at least $\lfloor r(k+1)\rfloor$ indices $i\in\{0,\dots,k\}$ satisfy $\cos\theta_i\ge\kappa$ and $\rho\le q_i/\cos\theta_i\le\sigma$. Then for every $k\in\mathbb N$
--   $$f(x_{k+1})-f(x^*)\le\Big(1-\frac{1-c_2}{M}\,c_1\,\frac{\kappa^2\rho}{\sigma}\,2m\Big)^{\lfloor r(k+1)\rfloor}\big(f(x_0)-f(x^*)\big).$$
--
--   This is the final display of the convergence proof: combined with the good-index property it yields the R-linear rate of Proposition 10.
--
--   **Formalization Note** The paper prints the left-hand side as $f(x_k)-f(x^*)$. The $\lfloor r(k+1)\rfloor$ good indices lie in $\{0,\dots,k\}$, and the decrease obtained at index $i$ improves $x_{i+1}$, not $x_i$; for $f(x_k)$ only the good indices in $\{0,\dots,k-1\}$ count (for instance with $k=1$, $r\ge1/2$ and the single good index $i=1$, the printed bound on $f(x_1)$ is not implied). The statement is therefore made for $f(x_{k+1})$. It is conditional on the good-index property, which is a separate milestone. The floor is the natural-number floor.
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

theorem rate_display
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hiso : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), ‖T k v‖ = ‖v‖)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v)
    (m Mc : ℝ) (hconv : UniformlyConvexOnSublevel f R x m Mc)
    (xstar : M) (hmin : ∀ y : M, f xstar ≤ f y)
    (hreach : ∀ k, ∃ q : TangentSpace 𝓘(ℝ, E) (x k), R (x k) q = xstar)
    (r κ ρ σ : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) (hκ : 0 < κ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hgood : HasGoodIndices (cosTheta x p α B) (rayleighQ x p α B) r κ ρ σ) :
    ∀ k : ℕ, f (x (k + 1)) - f xstar ≤
      (1 - (1 - c₂) / Mc * c₁ * (κ ^ 2 * ρ / σ) * (2 * m)) ^ ⌊r * (k + 1)⌋₊ *
        (f (x 0) - f xstar) := by sorry

end RiemOpt.BFGS
