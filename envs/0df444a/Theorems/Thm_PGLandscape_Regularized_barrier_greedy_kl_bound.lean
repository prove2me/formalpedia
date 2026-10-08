-- Prove2me | Theorems.Thm_PGLandscape_Regularized_barrier_greedy_kl_bound
-- name    : PGLandscape.Regularized.barrier_greedy_kl_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:06.404982+00:00
-- url     : https://prove2.me/theorems/da616324-d062-45f1-afee-920fb465bf31
-- title:
--   Step 3, p. 45 — the barrier-greedy π_λ of (36) satisfies λ·D(U‖π_λ(s)) ≤ λ log(1 + c/λ), c = 2 max|g_{s,i}|/(1−γ)
-- statement:
--   In the regularized finite MDP of Example 4 (with $\mathcal S$ and the action set nonempty), let $\lambda>0$, let $\pi_0$ be an optimal policy of the unregularized problem with optimal state-action cost-to-go $Q^*_0$, and let $\pi_\lambda$ be a barrier-greedy policy as in (36). Put
--
--   $$
--   c=\frac{2\,\max_{s,i}|g_{s,i}|}{1-\gamma}.
--   $$
--
--   Then for every state $s$,
--
--   $$
--   \lambda\cdot D(U\|\pi_\lambda(s))\le\lambda\log\Big(1+\frac c\lambda\Big).
--   $$
--
--   In particular $\pi_\lambda(s)$ lies in the open simplex. Combined with the cost decomposition (34) and the bound (35), this controls $\ell_\lambda(\pi_\lambda)$ in Step 3 of the proof of Lemma 10.
--
--   **Formalization Note** The left-hand side is evaluated in $[0,\infty]$, so the bound also asserts that $D(U\|\pi_\lambda(s))$ is finite.
-- source:
--   arXiv:1906.01786v3, App. E.2, proof of Lemma 10, Step 3, p. 45

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model
open FoundationsML.ReinforcementLearning
open scoped ENNReal

namespace PGLandscape.Regularized

/-- Step 3, p. 45: the barrier-greedy policy `π_λ` of (36) satisfies
`λ · D(U‖π_λ(s)) ≤ λ log(1 + c/λ)` at every state, with `c = 2 (max_{s,i} |g_{s,i}|)/(1 − γ)`. -/
theorem barrier_greedy_kl_bound {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    [Nonempty S] [Nonempty I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 < lam)
    (π₀ : S → I → ℝ) (hπ₀ : IsCostOptimal P gs γ π₀)
    (πlam' : S → I → ℝ) (hgreedy : IsBarrierGreedy P gs γ lam π₀ πlam') :
    ∀ s : S, ENNReal.ofReal lam * klUniform (πlam' s) ≤
      ENNReal.ofReal (lam * Real.log (1 + costConst gs γ / lam)) := by sorry

end PGLandscape.Regularized
