-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_splitting_compl
-- name    : TheoryOfGames.Decomposition.splitting_compl
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:15:11.878327+00:00
-- url     : https://prove2.me/theorems/76ed9d16-5c74-4728-852c-cba91eafda04
-- title:
--   (43:A) — J is a splitting set iff its complement I − J is one
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$. A set $J \subseteq I$ is a splitting set if and only if its complement $K = I - J$ is one:
--   $$J \text{ splitting} \iff I - J \text{ splitting}.$$
--
--   That a set of players is self-contained is the same statement as that the complement is self-contained.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 353, 43.2.1, (43:A)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:A), 43.2.1: `J` is a splitting set if and only if its complement `K = I - J` is one. -/
theorem splitting_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) :
    IsSplitting v J ↔ IsSplitting v Jᶜ := by sorry

end TheoryOfGames.Decomposition
