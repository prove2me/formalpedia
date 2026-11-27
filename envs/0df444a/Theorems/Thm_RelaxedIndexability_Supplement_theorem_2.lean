-- Prove2me | Theorems.Thm_RelaxedIndexability_Supplement_theorem_2
-- name    : RelaxedIndexability.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:05:07.651901+00:00
-- url     : https://prove2.me/theorems/370b52c9-1653-447f-bc79-6f2408c3a62d
-- title:
--   Theorem 2 — the restless bandit is indexable if $\beta\le1/2$
-- statement:
--   Consider a restless bandit with $N$ arms, each with its own number of states, row-stochastic transition matrix and reward vector, observed only when activated, and a common discount factor $\beta$ with
--
--   $$
--   0<\beta\le\tfrac12.
--   $$
--
--   Then the bandit is indexable (Definition 1): for every arm, the passive set $P(m)$ of the single-armed bandit with subsidy $m$ increases monotonically with $m$, from $\emptyset$ to the whole belief simplex.
--
--   Indexability makes the Whittle index well defined for every belief, so the Whittle index policy is available for every partially observable restless bandit with a small enough discount factor.
--
--   Differences from the source:
--   - generalization: P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: the theorem does not use them; every row-stochastic P and every B include the source's case
--   - generalization: the paper has a positive number of arms, each with a positive number of states → N and each arm's K are natural numbers and may be 0; reason: the empty-arm and empty-state conclusions are vacuous, while every source bandit is included
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Theorem 2, p.16; proof EC.4, pp.ec8–ec9

import Mathlib
import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_Supplement_Indexable

namespace RelaxedIndexability.Supplement

/-- **Theorem 2** (Liu, arXiv:2107.11939v4, Theorem 2, p.16; proof EC.4, pp.ec8–ec9): the restless
bandit is indexable (Definition 1) if `β ≤ 1/2`. For every number of arms, every arm and every
`0 < β ≤ 1/2`, the passive set increases monotonically from `∅` to the whole belief simplex.

**Formalization Note.** `β = 1/2` is included; `0 < β` is the standing assumption `β ∈ (0, 1)` of
p.6. -/
theorem theorem_2 (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) {N : ℕ}
    (arms : Fin N → RelaxedIndexability.Arm) :
    Indexable β arms := by sorry

end RelaxedIndexability.Supplement
