-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_splitting_empty_univ
-- name    : TheoryOfGames.Decomposition.splitting_empty_univ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:17:28.796978+00:00
-- url     : https://prove2.me/theorems/2c7dbd42-45f0-445b-a392-d5f5e456e5c4
-- title:
--   (43:B) — ⊖ and I are splitting sets
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$. Then the empty set $\ominus$ and the whole set $I$ are splitting sets:
--   $$v(S \cup T) = v(S) + v(T) \quad \text{whenever } S \subseteq \ominus,\ T \subseteq I, \text{ or } S \subseteq I,\ T \subseteq \ominus.$$
--
--   These are the trivial splitting sets; a game with no others is indecomposable (43.3.1).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 353, 43.2.1, (43:B)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:B), 43.2.1: `⊖` and `I` are splitting sets. -/
theorem splitting_empty_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    IsSplitting v ∅ ∧ IsSplitting v Finset.univ := by sorry

end TheoryOfGames.Decomposition
