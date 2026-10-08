-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_lineSet_isSolution
-- name    : TheoryOfGames.ThreePerson.lineSet_isSolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:37:47.574075+00:00
-- url     : https://prove2.me/theorems/4886e360-b3d8-43ac-b69d-e9de0fdd592d
-- title:
--   (32:A) — for −1 ≦ c < ½ the imputations with αᵢ = c form a solution
-- statement:
--   In the reduced essential zero-sum three-person game (32:1), let $c$ be a number with
--   $$\text{(32:8)}\quad -1 \leqq c < \tfrac12 ,$$
--   and let $i \in \{1, 2, 3\}$. Then the set of all imputations $\vec\alpha$ with $\alpha_i = c$ — the set (32:7), (32:7\*) or (32:7\*\*) for $i = 1, 2, 3$ — is a solution in the sense of (30:5:a), (30:5:b).
--
--   These are the book's "discriminatory" solutions: player $i$ is assigned the fixed amount $c$ and the other two divide $-c$ in every possible way. The bound $c < \tfrac12$ is strict.
--
--   **Formalization Note** Players $1, 2, 3$ are indices `0, 1, 2`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 287–288, 32.2.2, (32:7), (32:7*), (32:7**), (32:8); p. 288, 32.2.3, (32:A)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

namespace TheoryOfGames.ThreePerson

/-- (32:A) with (32:7), (32:7*), (32:7**), (32:8), 32.2.2: for every `c` with `-1 ≦ c < ½` and
every player `i`, the set of all imputations with `αᵢ = c` is a solution of the reduced
essential zero-sum three-person game (32:1). -/
theorem lineSet_isSolution (i : Fin 3) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c < 1 / 2) :
    IsSolution redV (lineSet i c) := by sorry

end TheoryOfGames.ThreePerson
