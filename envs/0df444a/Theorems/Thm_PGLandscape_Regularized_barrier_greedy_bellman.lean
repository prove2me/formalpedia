-- Prove2me | Theorems.Thm_PGLandscape_Regularized_barrier_greedy_bellman
-- name    : PGLandscape.Regularized.barrier_greedy_bellman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:30.264803+00:00
-- url     : https://prove2.me/theorems/d6924987-bac6-4c5d-8bac-03424ec45554
-- title:
--   (37), p. 44 — the barrier-greedy π_λ of (36) satisfies Σ_i Q*_0(s,e_i)π_λ(i|s) ≤ min_a Σ_i Q*_0(s,e_i)a_i + λ, i.e. T^{π_λ}_0 J*_0 ≤ J*_0 + λe
-- statement:
--   In the regularized finite MDP of Example 4, let $\lambda>0$, let $\pi_0$ be an optimal policy of the unregularized problem, so that $J^*_0=J_{0,\pi_0}$ and $Q^*_0(s,e_i)=g_{s,i}+\gamma\sum_{s'}P(s'|s,e_i)J^*_0(s')$, and let $\pi_\lambda$ be a policy constructed as in (36): at every state $s$,
--
--   $$
--   \pi_\lambda(s)\in\arg\min_{a\in\Delta_{k-1}}\ \sum_{i=1}^kQ^*_0(s,e_i)a_i+\lambda\,D(U\|a).
--   $$
--
--   Then for every state $s$,
--
--   $$
--   \sum_{i=1}^kQ^*_0(s,e_i)\,\pi_\lambda(i|s)\le\min_{a\in\Delta_{k-1}}\sum_{i=1}^kQ^*_0(s,e_i)\,a_i+\lambda,
--   \qquad\text{and}\qquad
--   \sum_{i=1}^kQ^*_0(s,e_i)\,\pi_\lambda(i|s)\le J^*_0(s)+\lambda .
--   $$
--
--   In Bellman-operator notation the second inequality is $T^{\pi_\lambda}_0J^*_0\le T_0J^*_0+\lambda e=J^*_0+\lambda e$, with $e$ the all-ones vector. The first is the duality-gap bound of the log-barrier method with $k$ inequality constraints and barrier weight $\lambda/k$.
--
--   **Formalization Note** The minimum over the simplex is written as "for every $a\in\Delta_{k-1}$". The objective of (36) is evaluated in $[0,\infty]$ (the $Q$-values are nonnegative because the costs are). The paper's proof of the first inequality cites Boyd and Vandenberghe, *Convex Optimization* (2004), p. 566.
-- source:
--   arXiv:1906.01786v3, App. E.2, proof of Lemma 10, Step 2, display before (37) and (37), p. 44

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model
open FoundationsML.ReinforcementLearning
open scoped ENNReal

namespace PGLandscape.Regularized

/-- Step 2, p. 44, display before (37) and (37): for the barrier-greedy policy `π_λ` of (36),
`Σ_i Q*_0(s, e_i) π_λ(i|s) ≤ min_{a∈∆_{k−1}} Σ_i Q*_0(s, e_i) a_i + λ`, i.e.
`T^{π_λ}_0 J*_0 ≤ T_0 J*_0 + λe = J*_0 + λe`. -/
theorem barrier_greedy_bellman {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 < lam)
    (π₀ : S → I → ℝ) (hπ₀ : IsCostOptimal P gs γ π₀)
    (πlam' : S → I → ℝ) (hgreedy : IsBarrierGreedy P gs γ lam π₀ πlam') :
    ∀ s : S,
      (∀ a : I → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i = 1 →
        ∑ i, QFunction π₀ P gs γ s i * πlam' s i ≤ ∑ i, QFunction π₀ P gs γ s i * a i + lam) ∧
      ∑ i, QFunction π₀ P gs γ s i * πlam' s i ≤ PolicyValue π₀ P gs γ s + lam := by sorry

end PGLandscape.Regularized
