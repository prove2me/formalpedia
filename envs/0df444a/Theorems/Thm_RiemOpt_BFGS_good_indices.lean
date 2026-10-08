-- Prove2me | Theorems.Thm_RiemOpt_BFGS_good_indices
-- name    : RiemOpt.BFGS.good_indices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:37.590059+00:00
-- url     : https://prove2.me/theorems/a5da43bf-fa69-4b24-9d87-f6b543fad559
-- title:
--   Appendix A, proof of Proposition 10, pp. 621–622 — for each 0<r<1, ⌊r(k+1)⌋ indices i ≤ k with cos θ_i ≥ κ and ρ ≤ q_i/cos θ_i ≤ σ
-- statement:
--   Consider a non-terminating Riemannian BFGS run with Wolfe steps (definition **Setting**) under the hypotheses of Proposition 10 apart from the minimizer: the transports $T_k$ are isometries, $B_0$ is symmetric and coercive, and the $f_{R_{x_k}}$ are uniformly convex on the $f(x_0)$-sublevel set with constants $0<m<M$. Let $\cos\theta_i$ and $q_i$ be the angle and Rayleigh quotient
--   $$\cos\theta_i=\frac{B_i(s_i,s_i)}{\|s_i\|_{x_i}\|B_i(s_i,\cdot)\|_{x_i}},\qquad q_i=\frac{B_i(s_i,s_i)}{\|s_i\|^2_{x_i}}.$$
--   Then for every $0<r<1$ there are constants $\kappa,\rho,\sigma>0$ such that for every $k\in\mathbb N$ at least $\lfloor r(k+1)\rfloor$ indices $i\in\{0,\dots,k\}$ satisfy
--   $$\cos\theta_i\ge\kappa\qquad\text{and}\qquad \rho\le\frac{q_i}{\cos\theta_i}\le\sigma.$$
--
--   This is the Byrd–Nocedal-type "good iterates" property, transferred to manifolds and infinite dimensions; it is the step that replaces eigenvalue bounds on the $B_k$, which are not available for BFGS.
--
--   **Formalization Note** The constants $\kappa,\rho,\sigma$ may depend on the run and on $r$ but not on $k$. The set of good indices is a `Finset` inside $\{0,\dots,k\}$ of cardinality at least $\lfloor r(k+1)\rfloor$ (natural-number floor). The paper's argument goes through traces and determinants of trace-class perturbations of the identity, which are not part of the statement.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), pp. 621–622, Appendix A, proof of Proposition 10

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem good_indices
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hiso : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), ‖T k v‖ = ‖v‖)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v)
    (m Mc : ℝ) (hconv : UniformlyConvexOnSublevel f R x m Mc) :
    ∀ r : ℝ, 0 < r → r < 1 → ∃ κ ρ σ : ℝ, 0 < κ ∧ 0 < ρ ∧ 0 < σ ∧
      HasGoodIndices (cosTheta x p α B) (rayleighQ x p α B) r κ ρ σ := by sorry

end RiemOpt.BFGS
