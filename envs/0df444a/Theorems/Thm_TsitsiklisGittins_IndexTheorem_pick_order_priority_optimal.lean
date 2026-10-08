-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_pick_order_priority_optimal
-- name    : TsitsiklisGittins.IndexTheorem.pick_order_priority_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:23.209175+00:00
-- url     : https://prove2.me/theorems/35912e1b-0cc4-44d8-a5bc-614b9e5f8b22
-- title:
--   Any priority policy ordering the states as the index algorithm picks them is optimal
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with finite nonempty state spaces, and let $s_0,s_1,\dots,s_{N-1}$ be the order in which a run of the index algorithm picks the states of $\mathcal X$. Let $\pi$ be a priority policy whose priority order agrees with the picking order: states picked earlier have strictly higher priority,
--   $$
--   a<b\ \Longrightarrow\ \operatorname{rank}(s_b)<\operatorname{rank}(s_a),
--   $$
--   and $\pi$ always plays the bandit whose current state has the highest rank. Then $\pi$ is optimal.
--
--   This is what the proof of Theorem 2.1 shows when the induction always removes the state picked by the index algorithm; together with the characterization of the picking orders through the indices it gives Theorem 2.2.
--
--   **Formalization Note** The statement holds for every run of the index algorithm, whatever the tie choices in its step (a). Optimality is over stationary deterministic policies and for every initial joint state.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 198 (PDF p. 5), Section 2, proof of Theorem 2.2, first sentence

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: any priority policy that orders the states
in the same order as they are picked by (a run of) the index algorithm is optimal. -/
theorem pick_order_priority_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ)
    (hord : ∀ (a b : ℕ) (ha : a < seq.length) (hb : b < seq.length), a < b → rank seq[b] < rank seq[a])
    (π : Policy n X) (hπ : FollowsRank rank π) :
    B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem
