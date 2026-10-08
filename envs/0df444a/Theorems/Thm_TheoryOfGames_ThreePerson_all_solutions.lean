-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_all_solutions
-- name    : TheoryOfGames.ThreePerson.all_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:37:43.422656+00:00
-- url     : https://prove2.me/theorems/32269b27-97a2-4baf-9624-5b2a54a995e7
-- title:
--   (32:A), (32:B) — the complete list of solutions of the essential zero-sum three-person game
-- statement:
--   Consider the essential zero-sum three-person game in its reduced form with $\gamma = 1$: players $1, 2, 3$ and characteristic function
--   $$\text{(32:1)}\quad v(S) = 0,\ -1,\ 1,\ 0 \quad\text{when } S \text{ has } 0, 1, 2, 3 \text{ elements}.$$
--   Its imputations are the vectors with (32:2) $\alpha_1, \alpha_2, \alpha_3 \geqq -1$ and (32:3) $\alpha_1 + \alpha_2 + \alpha_3 = 0$. A set $V$ is a solution (30:5) if and only if it is one of the following:
--
--   1. **(32:A)** for some $c$ with (32:8) $-1 \leqq c < \tfrac12$ and some player $i \in \{1, 2, 3\}$, the set of all imputations with $\alpha_i = c$ (the sets (32:7), (32:7\*), (32:7\*\*));
--   2. **(32:B)** the set (32:6)
--   $$\{-1, \tfrac12, \tfrac12\},\quad \{\tfrac12, -1, \tfrac12\},\quad \{\tfrac12, \tfrac12, -1\}.$$
--
--   "This is a complete list of solutions": both directions are asserted — each listed set is a solution, and there are no others. It is the first game for which the book determines all solutions, and it shows that solutions are not unique: besides the symmetric solution (32:B) there are infinitely many discriminatory ones.
--
--   **Formalization Note** Players $1, 2, 3$ are indices `0, 1, 2 : Fin 3`; the characteristic function is `redV`, the set (32:6) is `middlePointsSet`, and the set of imputations with `α i = c` is `lineSet i c`. The statement is for the reduced form (32:1) exactly as in the book; by (31:Q) and the reduction of 27.1 with the choice of unit $\gamma = 1$ (27.3.2), it describes the solutions of every essential zero-sum three-person game, but that transfer is not part of this statement.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 282, (32:1); p. 287, (32:6), (32:7); p. 288, (32:8), 32.2.3, (32:A), (32:B)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

namespace TheoryOfGames.ThreePerson

/-- (32:A), (32:B), 32.2.3: a complete list of solutions of the essential zero-sum
three-person game in the reduced form (32:1) with `γ = 1`: a set `V` of vectors is a solution
if and only if it is the set (32:6), or it is one of the sets (32:7), (32:7*), (32:7**)
(all imputations with `αᵢ = c`) for some `c` fulfilling (32:8) `-1 ≦ c < ½`. -/
theorem all_solutions (V : Set (Fin 3 → ℝ)) :
    IsSolution redV V ↔
      V = middlePointsSet ∨
        ∃ i : Fin 3, ∃ c : ℝ, -1 ≤ c ∧ c < 1 / 2 ∧ V = lineSet i c := by sorry

end TheoryOfGames.ThreePerson
