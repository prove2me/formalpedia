-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_theorem2_2_index_priority_optimal
-- name    : TsitsiklisGittins.IndexTheorem.theorem2_2_index_priority_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:40.218086+00:00
-- url     : https://prove2.me/theorems/21e475b2-e007-44ff-8929-201a98aa200a
-- title:
--   Theorem 2.2 (Gittins index theorem) — every priority policy giving higher-index states higher priority is optimal
-- statement:
--   Consider $n\ge1$ semi-Markov bandit processes with finite nonempty state spaces $\mathcal X_1,\dots,\mathcal X_n$, discount rate $\beta>0$, and the objective of maximizing the expected discounted reward $\mathbb E\big[\sum_{i\ge1}R_ie^{-\beta t_i}\big]$ for every initial state. Let the index $\gamma(x)$ of each state $x\in\mathcal X$ be determined by the index algorithm. Then any priority policy in which states with a higher index have higher priority is optimal: if $\pi$ always plays the bandit whose current state is ranked highest under an ordering of $\mathcal X$ with
--   $$
--   \gamma(y)<\gamma(x)\ \Longrightarrow\ y\ \text{is ranked below}\ x,
--   $$
--   then $J_{\pi'}(z)\le J_\pi(z)$ for every policy $\pi'$ and every initial state $z$.
--
--   This is the Gittins index theorem for semi-Markov bandits: an optimal priority order is obtained by sorting the states by indices that, by the reduction formulas, can be computed separately for each bandit.
--
--   **Formalization Note** The index is that of an arbitrary run of the index algorithm (any tie choice in step (a)); states with equal indices may be ordered either way. The ordering is an injective ranking of $\mathcal X=$ `Σ i, X i`. Optimality is over the paper's stationary deterministic policies, for every initial joint state, with $J$ computed from the one-play moments by the first-step recursion (see the definition module). Bandits are indexed by `Fin n`.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 198 (PDF p. 5), Theorem 2.2

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Theorem 2.2 of Tsitsiklis (1994), p. 198: let the index `γ` of each state be determined by
(any run of) the index algorithm. Then any priority policy in which states with a higher index
have higher priority is optimal. -/
theorem theorem2_2_index_priority_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ) (hinj : Function.Injective rank)
    (hcompat : ∀ x y : Σ i, X i, γ y < γ x → rank y < rank x)
    (π : Policy n X) (hπ : FollowsRank rank π) :
    B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem
