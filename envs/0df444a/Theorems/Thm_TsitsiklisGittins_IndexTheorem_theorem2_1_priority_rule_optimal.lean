-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_theorem2_1_priority_rule_optimal
-- name    : TsitsiklisGittins.IndexTheorem.theorem2_1_priority_rule_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:22.286978+00:00
-- url     : https://prove2.me/theorems/fe831772-527d-4693-8c9c-1a098d760cbf
-- title:
--   Theorem 2.1 — for finite state spaces some priority rule is optimal
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with $n\ge1$ bandits, discount rate $\beta>0$ and state spaces $\mathcal X_1,\dots,\mathcal X_n$. If each $\mathcal X_i$, $i=1,\dots,n$, is finite (and nonempty), then there exists a priority rule which is optimal:
--   $$
--   \exists\,\pi\ \text{priority rule with}\ J_{\pi'}(z)\le J_\pi(z)\ \text{for every policy}\ \pi'\ \text{and every initial state}\ z .
--   $$
--
--   This is the paper's basic result; Theorem 2.2 refines it by identifying an optimal priority order through indices computed bandit by bandit.
--
--   **Formalization Note** Finiteness is the `Fintype` instance on each state type. A priority rule is a policy that, for some injective ranking of $\mathcal X$, always plays the bandit whose current state has the highest rank. Optimality is over stationary deterministic policies and for every initial joint state. Bandits are indexed by `Fin n`.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 196 (PDF p. 3), Theorem 2.1

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit

namespace TsitsiklisGittins.IndexTheorem

/-- Theorem 2.1 of Tsitsiklis (1994), p. 196: if each `𝒳ᵢ` is finite, there exists a priority
rule which is optimal. -/
theorem theorem2_1_priority_rule_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X) :
    ∃ π : Policy n X, IsPriorityRule π ∧ B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem
