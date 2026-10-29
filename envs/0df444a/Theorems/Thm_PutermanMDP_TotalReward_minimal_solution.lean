-- Prove2me | Theorems.Thm_PutermanMDP_TotalReward_minimal_solution
-- name    : PutermanMDP.TotalReward.minimal_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:02.606715+00:00
-- url     : https://prove2.me/theorems/e636399b-3d54-4175-af44-3a9145b5cfe1
-- title:
--   Theorem 7.2.3(a) — Minimal nonnegative Bellman solution
-- statement:
--   In a positive bounded model on nonempty countable state and action spaces, the optimal total-reward value belongs to the class $V^+$ of pointwise-finite nonnegative functions and is its least Bellman fixed point:
--   $$
--   v^*\in V^+,\qquad\mathcal Lv^*=v^*,\qquad
--   \forall v\in V^+,\quad \mathcal Lv=v\Longrightarrow v^*\le v.
--   $$
--   The optimal value is defined by the supremum of policy rewards. This result characterizes that value without asserting uniqueness of all fixed points.
--
--   **Formalization Note** This item is precisely part (a) of Theorem 7.2.3. Part (b) is outside this item and is separately discussed in finding F2. Finiteness and nonnegativity of $v^*$ are conclusions, not assumptions.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 286 (PDF 302), Theorem 7.2.3(a)

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Bellman

namespace PutermanMDP.TotalReward

/-- Theorem 7.2.3(a), including membership in the pointwise-finite class V⁺.
Part (b), about arbitrary stationary policies, is not asserted by this item. -/
theorem minimal_solution {S : Type*} {A : S → Type*}
    [Countable S] [Nonempty S] [∀ s, Countable (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (hM : PositiveBounded M) :
    InVPlus (optimalValue M) ∧
    bellman M (optimalValue M) = optimalValue M ∧
    ∀ v : S → EReal, InVPlus v → bellman M v = v → optimalValue M ≤ v := by sorry

end PutermanMDP.TotalReward
