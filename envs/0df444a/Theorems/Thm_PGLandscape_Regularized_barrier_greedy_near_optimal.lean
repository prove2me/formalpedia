-- Prove2me | Theorems.Thm_PGLandscape_Regularized_barrier_greedy_near_optimal
-- name    : PGLandscape.Regularized.barrier_greedy_near_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:56.168826+00:00
-- url     : https://prove2.me/theorems/4b5f32dd-4b78-4e77-b304-bcedb382ad2d
-- title:
--   (35), p. 44 — the barrier-greedy π_λ of (36) satisfies ℓ_0(π_λ) ≤ min_{π∈Π} ℓ_0(π) + λ
-- statement:
--   In the regularized finite MDP of Example 4, let $\lambda>0$, let $\pi_0$ be an optimal policy of the unregularized problem with optimal state-action cost-to-go $Q^*_0$, and let $\pi_\lambda$ be a barrier-greedy policy as in (36): $\pi_\lambda(s)$ minimizes $a\mapsto\sum_{i}Q^*_0(s,e_i)a_i+\lambda D(U\|a)$ over $\Delta_{k-1}$ at every state $s$. Then
--
--   $$
--   \ell_0(\pi_\lambda)\le\min_{\pi\in\Pi}\ell_0(\pi)+\lambda ,
--   $$
--
--   where $\ell_0(\pi)=(1-\gamma)\sum_s\rho(s)J_{0,\pi}(s)$ is the unregularized discounted average cost and $\Pi$ is the set of all stationary policies.
--
--   The policy $\pi_\lambda$ is a comparison policy: its existence with this suboptimality gap is Step 2 of the proof of Lemma 10.
--
--   **Formalization Note** The minimum over $\Pi$ is written as "$\le\ell_0(\pi)+\lambda$ for every policy $\pi$".
-- source:
--   arXiv:1906.01786v3, App. E.2, proof of Lemma 10, Step 2, (35), p. 44

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model
open FoundationsML.ReinforcementLearning
open scoped ENNReal

namespace PGLandscape.Regularized

/-- (35), Step 2, p. 44: the barrier-greedy policy `π_λ` of (36) satisfies
`ℓ_0(π_λ) ≤ min_{π∈Π} ℓ_0(π) + λ`. -/
theorem barrier_greedy_near_optimal {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 < lam)
    (π₀ : S → I → ℝ) (hπ₀ : IsCostOptimal P gs γ π₀)
    (πlam' : S → I → ℝ) (hgreedy : IsBarrierGreedy P gs γ lam π₀ πlam') :
    ∀ π : S → I → ℝ, IsPolicy π → loss0 P gs γ ρ πlam' ≤ loss0 P gs γ ρ π + lam := by sorry

end PGLandscape.Regularized
