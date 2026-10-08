-- Prove2me | Theorems.Thm_RiemOpt_BFGS_lemma_9
-- name    : RiemOpt.BFGS.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:49.983981+00:00
-- url     : https://prove2.me/theorems/f2362c79-5dd8-4e13-836b-e54b40a47be6
-- title:
--   Lemma 9 — Riemannian BFGS with Wolfe steps: $y_ks_k>0$ and every $B_k$ is coercive
-- statement:
--   Consider a non-terminating run of Algorithm 1 with the BFGS search direction and Wolfe step size control on a Riemannian manifold $\mathcal M$ modelled on a Hilbert space, as in the definition **Setting**: iterates $x_k$, directions $p_k$ with $B_k(p_k,\cdot)=-\mathrm Df(x_k)$, steps $\alpha_k>0$ satisfying (1a)–(1b), BFGS updates of the bilinear forms $B_k$ through invertible transports $T_k:T_{x_k}\mathcal M\to T_{x_{k+1}}\mathcal M$, and $s_k=\alpha_kp_k$, $y_k=\mathrm Df_{R_{x_k}}(s_k)-\mathrm Df_{R_{x_k}}(0)$.
--
--   Assume that the operator norms $\|T_k\|$ and $\|T_k^{-1}\|$ are uniformly bounded in $k$, and that $B_0$ is symmetric and coercive: there is $c>0$ with $B_0(v,v)\ge c\|v\|_{x_0}^2$ for all $v$. Then for every $k\in\mathbb N$
--   $$y_ks_k>0,$$
--   and $B_k$ is coercive: there is $c_k>0$ with $B_k(v,v)\ge c_k\|v\|_{x_k}^2$ for all $v\in T_{x_k}\mathcal M$.
--
--   This is the well-posedness result for the Riemannian BFGS iteration: positivity of the curvature pair keeps the update defined, and coercivity of $B_k$ makes $p_k$ a descent direction.
--
--   **Formalization Note** The $B_k$ are given as data satisfying the update formula, so the "well-defined" part of the lemma (nonzero denominators) is expressed by $y_ks_k>0$ together with coercivity, which gives $B_k(s_k,s_k)>0$. "Bounded" is automatic, since each $B_k$ is a continuous bilinear form. Symmetry of $B_0$ is not printed in Lemma 9 but is used by its proof (the Lax–Milgram representation $\hat B_{k+1}$ and the Sherman–Morrison formula (7) are those of a self-adjoint $\hat B_k$); for a non-symmetric coercive $B_0$ the updated form $B_1$ can fail to be coercive. The paper's "the $f_{R_{x_k}}$ are assumed smooth" is weakened to $C^2$.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), pp. 606–607, Lemma 9

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem lemma_9
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))
    (hrun : IsBFGSRun f R c₁ c₂ x p α B T)
    (hT : ∃ C : ℝ, ∀ k,
      ‖(T k : TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1)))‖ ≤ C ∧
      ‖((T k).symm : TangentSpace 𝓘(ℝ, E) (x (k + 1)) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k))‖ ≤ C)
    (hB0symm : ∀ v w : TangentSpace 𝓘(ℝ, E) (x 0), B 0 v w = B 0 w v)
    (hB0 : ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x 0), c * ‖v‖ ^ 2 ≤ B 0 v v) :
    ∀ k, 0 < yVec f R x p α k (sVec x p α k) ∧
      ∃ c > 0, ∀ v : TangentSpace 𝓘(ℝ, E) (x k), c * ‖v‖ ^ 2 ≤ B k v v := by sorry

end RiemOpt.BFGS
