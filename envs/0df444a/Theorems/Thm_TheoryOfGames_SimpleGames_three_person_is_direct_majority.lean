-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_three_person_is_direct_majority
-- name    : TheoryOfGames.SimpleGames.three_person_is_direct_majority
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:00:48.161+00:00
-- url     : https://prove2.me/theorems/8d4f531b-6f10-4539-af7b-39af43fd915b
-- title:
--   (50:A) — the essential three-person game is simple and is the direct majority game
-- statement:
--   Let $v$ be a characteristic function (25:3:a)–(25:3:c) of an essential zero-sum three-person game. Then the game is simple, and it is the direct majority game of three participants: its winning coalitions are exactly the sets with more than $\tfrac32$ elements,
--   $$W_\Gamma = \{ S \subseteq \{1,2,3\} : |S| > \tfrac32 \}.$$
--
--   This identifies the smallest simple game and is the starting example of the majority games of §50.
--
--   **Formalization Note** Players $1, 2, 3$ are `0, 1, 2 : Fin 3`. The word "unique" refers to the uniqueness of the essential three-person game up to strategic equivalence, established in 29.1 and not restated here.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 432, (50:A); p. 431, 50.1.1 (direct majority game)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (50:A), p. 432: the (unique) essential three-person game is simple; it is the direct
majority game of three participants, i.e. its `W_Γ` is the set of all `S` with `> 3/2`
elements (50.1.1). Players `1, 2, 3` are `0, 1, 2 : Fin 3`. -/
theorem three_person_is_direct_majority (v : Finset (Fin 3) → ℝ) (hv : IsCharFunction v)
    (hess : ¬ IsInessential v) :
    IsSimple v ∧ winningSets v = {S | (3 : ℝ) / 2 < (S.card : ℝ)} := by sorry

end TheoryOfGames.SimpleGames
