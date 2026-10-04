-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_minimal_cover
-- name    : TheoryOfGames.Decomposition.minimal_cover
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:29:05.538165+00:00
-- url     : https://prove2.me/theorems/12a6a60a-d8ae-4d63-99ac-939971e3b0f3
-- title:
--   (43:G) — the sum of all minimal splitting sets is I
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$. Then the union ("sum") of all minimal splitting sets is $I$: every player $k \in I$ belongs to some minimal splitting set $J$,
--   $$\bigcup \{J : J \text{ a minimal splitting set}\} = I.$$
--
--   **Formalization Note** Since every minimal splitting set is a subset of $I$, "the sum is $I$" is stated as: for every player $k$ there is a minimal splitting set containing $k$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 355, 43.3.2, (43:G)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:G), 43.3.2: the sum of all minimal splitting sets is `I`, i.e. every player `k ∈ I`
belongs to some minimal splitting set. -/
theorem minimal_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (k : ι) :
    ∃ J : Finset ι, IsMinimalSplitting v J ∧ k ∈ J := by sorry

end TheoryOfGames.Decomposition
