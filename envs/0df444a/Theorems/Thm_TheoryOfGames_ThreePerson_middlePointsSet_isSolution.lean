-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_middlePointsSet_isSolution
-- name    : TheoryOfGames.ThreePerson.middlePointsSet_isSolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:37:24.574273+00:00
-- url     : https://prove2.me/theorems/78da37fd-b264-406c-9f9a-2f492d32d9af
-- title:
--   (32:B) — the set (32:6) is a solution of the reduced three-person game
-- statement:
--   In the reduced essential zero-sum three-person game (32:1), the set of the three imputations
--   $$\text{(32:6)}\quad \{-1, \tfrac12, \tfrac12\},\quad \{\tfrac12, -1, \tfrac12\},\quad \{\tfrac12, \tfrac12, -1\}$$
--   is a solution in the sense of (30:5:a), (30:5:b).
--
--   This is the solution the book had singled out heuristically in 29.1 (the set of Figure 51): each two-person coalition splits its gain equally and the excluded player gets $-1$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 287, 32.2.1, (32:6); p. 288, 32.2.3, (32:B)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

namespace TheoryOfGames.ThreePerson

/-- (32:B) with (32:6), 32.2.1: the set `{-1, ½, ½}, {½, -1, ½}, {½, ½, -1}` is a solution of
the reduced essential zero-sum three-person game (32:1). -/
theorem middlePointsSet_isSolution : IsSolution redV middlePointsSet := by sorry

end TheoryOfGames.ThreePerson
