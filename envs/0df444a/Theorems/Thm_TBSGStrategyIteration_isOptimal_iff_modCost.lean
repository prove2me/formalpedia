-- Prove2me | Theorems.Thm_TBSGStrategyIteration_isOptimal_iff_modCost
-- name    : TBSGStrategyIteration.isOptimal_iff_modCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:50:04.619766+00:00
-- url     : https://prove2.me/theorems/46203c3f-6074-42e0-9c5f-4f197d81f21f
-- title:
--   Lemma 3.7 — optimality condition via modified costs
-- statement:
--   Let $A^1 = \bigcup_{i \in S_1} A_i$ and $A^2 = \bigcup_{i \in S_2} A_i$ be the actions of players 1 and 2. A strategy profile $\pi$ is optimal if and only if
--   $$(c^\pi)_a \ge 0 \ \text{ for all } a \in A^1 \qquad \text{and} \qquad (c^\pi)_a \le 0 \ \text{ for all } a \in A^2 .$$
--   This local certificate of optimality ("no profitable switch") drives the analysis of strategy iteration.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 5, Lemma 3.7

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_modCost

namespace TBSGStrategyIteration

/-- Lemma 3.7 (optimality condition): a strategy profile `π` is optimal iff
`(c^π)_{A¹} ≥ 0` and `(c^π)_{A²} ≤ 0`, where `A¹` (`A²`) is the set of actions played from
states of player 1 (player 2) and `c^π` is the modified cost vector (Def. 3.3). -/
theorem isOptimal_iff_modCost {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π : Profile G) :
    IsOptimal G π ↔
      (∀ a : A, G.src a ∈ G.S1 → 0 ≤ modCost G π a) ∧
        (∀ a : A, G.src a ∉ G.S1 → modCost G π a ≤ 0) := by sorry

end TBSGStrategyIteration
