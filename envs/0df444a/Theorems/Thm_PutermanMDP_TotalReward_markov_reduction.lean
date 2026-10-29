-- Prove2me | Theorems.Thm_PutermanMDP_TotalReward_markov_reduction
-- name    : PutermanMDP.TotalReward.markov_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:02.505123+00:00
-- url     : https://prove2.me/theorems/16803208-66b3-49b2-a80a-08da04a97c99
-- title:
--   Proposition 7.1.1 — Markov policies suffice for total reward
-- statement:
--   Let $S$ and each nonempty action set $A_s$ be finite or countably infinite, with real rewards and stochastic transition rows. Suppose Assumption 7.1.1 holds: for every history-dependent randomized policy $\pi$ and initial state $s$, at least one of the expected accumulated positive and negative rewards is finite. Then for every state,
--   $$
--   v^*(s)=\sup_{\pi\in\Pi^{HR}}v^\pi(s)=\sup_{\pi\in\Pi^{MR}}v^\pi(s).
--   $$
--   Here $\Pi^{HR}$ consists of all admissible history-dependent randomized policies, and $\Pi^{MR}$ consists of all time-dependent randomized Markov policies. This allows pointwise total-reward optimization to be restricted to Markov policies.
--
--   **Formalization Note** Both suprema are extended-real suprema. The statement permits infinite values and asserts neither attainment nor the existence of one policy attaining the supremum at every state.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 280 (PDF 296), Proposition 7.1.1

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Model

namespace PutermanMDP.TotalReward

/-- Proposition 7.1.1. Equality of pointwise suprema does not assert that
one Markov policy attains them simultaneously at all states. -/
theorem markov_reduction {S : Type*} {A : S → Type*}
    [Countable S] [Nonempty S] [∀ s, Countable (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (hM : WellDefined M) (s : S) :
    optimalValue M s = (⨆ π : HRPolicy S A, policyValue M π s) ∧
    optimalValue M s = (⨆ π : MRPolicy S A, policyValue M (markovPolicy π) s) := by sorry

end PutermanMDP.TotalReward
