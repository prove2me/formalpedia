-- Prove2me | Theorems.Thm_TightQLearning_bellman_facts
-- name    : TightQLearning.bellman_facts
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:20.409772+00:00
-- url     : https://prove2.me/theorems/8c948be9-6a66-4c89-a113-3ae67d39fbdf
-- title:
--   §2, p.6 — Bellman facts: $\mathcal T(Q^\star)=Q^\star$, uniqueness, and a deterministic optimal policy
-- statement:
--   Let $\gamma\in(0,1)$ and let the rewards lie in $[0,1]$. Then:
--
--   1. $0\le V^\pi(s)\le\frac1{1-\gamma}$ and $0\le Q^\pi(s,a)\le\frac1{1-\gamma}$ for every policy $\pi$ and all $(s,a)$;
--   2. $Q^\star$ is a fixed point of the Bellman operator,
--   $$Q^\star(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)\max_{a'}Q^\star(s',a');$$
--   3. any solution of this equation equals $Q^\star$;
--   4. there is a deterministic policy $\pi^\star$ with $V^{\pi^\star}=V^\star$ and $Q^{\pi^\star}=Q^\star$;
--   5. $V^\star(s)=\max_aQ^\star(s,a)$, and $V^\star$, $Q^\star$ take values in $[0,\frac1{1-\gamma}]$.
--
--   Every later step of the analysis uses these facts: the recursion for $\Delta_t=Q_t-Q^\star$ starts from the Bellman equation, and $\pi^\star$ gives its lower half.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - encoding: max_π V^π, max_π Q^π → real suprema over the type of policies, with attainment by π⋆ stated as part of the theorem; reason: the family is bounded and nonempty, so the supremum is the page's maximum
--   - generalization: the page states the range of V^π and Q^π, attainment by a deterministic π⋆, and that Q⋆ is the unique fixed point of 𝒯 → the same, plus the two clauses V⋆(s) = max_a Q⋆(s,a) and 0 ≤ V⋆, Q⋆ ≤ 1/(1−γ); reason: the extra clauses follow from the page's facts (attainment by π⋆ and the range of V^π, Q^π) and are used on pp.12, 20; dropping them gives the page's statement
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_TightQLearning_vStar
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_detPolicy

open QLearning.Convergence

namespace TightQLearning

/-- Bellman facts of §2 (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.6) for `γ ∈ (0,1)` and
`r ∈ [0,1]`: `0 ≤ V^π, Q^π ≤ 1/(1−γ)`; `Q⋆` solves the Bellman equation `𝒯(Q⋆) = Q⋆`, and it is the
only solution; a deterministic policy `π⋆` attains `V⋆` and `Q⋆` simultaneously; and
`V⋆(s) = max_a Q⋆(s,a)`, with `0 ≤ V⋆, Q⋆ ≤ 1/(1−γ)`. -/
theorem bellman_facts {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    (∀ (π : Policy X A) (s : X), 0 ≤ valuePi M γ π s ∧ valuePi M γ π s ≤ 1 / (1 - γ)) ∧
    (∀ (π : Policy X A) (s : X) (a : A), 0 ≤ qPi M γ π s a ∧ qPi M γ π s a ≤ 1 / (1 - γ)) ∧
    IsOptimalQ M γ (qStar M γ) ∧
    (∀ Q : X → A → ℝ, IsOptimalQ M γ Q → Q = qStar M γ) ∧
    (∃ πs : X → A, (∀ s, valuePi M γ (detPolicy πs) s = vStar M γ s) ∧
      ∀ s a, qPi M γ (detPolicy πs) s a = qStar M γ s a) ∧
    (∀ s, vStar M γ s = vmax (qStar M γ) s) ∧
    (∀ s, 0 ≤ vStar M γ s ∧ vStar M γ s ≤ 1 / (1 - γ)) ∧
    (∀ s a, 0 ≤ qStar M γ s a ∧ qStar M γ s a ≤ 1 / (1 - γ)) := by sorry

end TightQLearning
