-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_exercise_10_7
-- name    : SuttonBartoRL.AverageReward.exercise_10_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:02:34.737986+00:00
-- url     : https://prove2.me/theorems/62c58064-71ad-4df9-aa26-4c2285923f26
-- title:
--   Exercise 10.7: differential values $-1/3, 0, 1/3$ in the three-state ring
-- statement:
--   In the ring Markov reward process $\mathsf A \to \mathsf B \to \mathsf C \to \mathsf A$ with reward $+1$ upon arrival in $\mathsf A$ and $0$ otherwise:
--   1. the average reward (10.6) is $\tfrac13$ from every starting state;
--   2. with $r(\pi) = \tfrac13$, the differential values (10.13) are
--   $$
--   v(\mathsf A) = -\tfrac13,\qquad v(\mathsf B) = 0, \qquad v(\mathsf C) = \tfrac13 .
--   $$
--
--   The book leaves the answer to the reader; it is computed here. The chain is periodic, so the limit (10.7) does not exist, but (10.13) gives well-defined differential values. The same ring is used in Exercise 10.8, which gives $\tfrac13$ as the true average reward.
--
--   **Formalization Note** $\mathsf A, \mathsf B, \mathsf C$ are the states `0, 1, 2` of `Fin 3` in `ringMRP`.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 10.7 with Eq. (10.13), p. 251 (no solution printed); average reward 1/3 stated in Exercise 10.8, p. 251

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward
import Definitions.Def_SuttonBartoRL_AverageReward_RingMRP

open Filter Topology

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), Exercise 10.7, p. 251 (answers not printed; computed here). In the ring
Markov reward process `A → B → C → A` with reward `+1` upon arrival in `A` (`A = 0`, `B = 1`,
`C = 2`), the average reward (10.6) is `1/3` from every state, and the differential values (10.13)
with `r(π) = 1/3` are `v(A) = −1/3`, `v(B) = 0`, `v(C) = 1/3`. -/
theorem exercise_10_7 :
    (∀ s : Fin 3, Tendsto (fun h : ℕ => (1 / (h : ℝ)) *
        ∑ t ∈ Finset.range h, ringMRP.expectedRewardAt ringPolicy t s) atTop (𝓝 (1 / 3))) ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 0 (-1 / 3) ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 1 0 ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 2 (1 / 3) := by sorry

end SuttonBartoRL.AverageReward
