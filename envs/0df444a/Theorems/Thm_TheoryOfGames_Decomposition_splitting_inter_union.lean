-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_splitting_inter_union
-- name    : TheoryOfGames.Decomposition.splitting_inter_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:19:28.326184+00:00
-- url     : https://prove2.me/theorems/0f6f5dad-26ad-49c5-9318-127605ff14d2
-- title:
--   (43:C) — J′ ∩ J″ and J′ ∪ J″ are splitting sets if J′, J″ are
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, and let $J'$, $J''$ be splitting sets. Then
--   $$J' \cap J'' \quad\text{and}\quad J' \cup J''$$
--   are splitting sets.
--
--   Together with (43:A), (43:B) this says that the splitting sets form a Boolean subalgebra of the subsets of $I$; it is the basic closure property from which (43:F)–(43:H) follow.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 354, 43.2.2, (43:C)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:C), 43.2.2: `J′ ∩ J″` and `J′ ∪ J″` are splitting sets if `J′`, `J″` are. -/
theorem splitting_inter_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J' J'' : Finset ι)
    (h' : IsSplitting v J') (h'' : IsSplitting v J'') :
    IsSplitting v (J' ∩ J'') ∧ IsSplitting v (J' ∪ J'') := by sorry

end TheoryOfGames.Decomposition
