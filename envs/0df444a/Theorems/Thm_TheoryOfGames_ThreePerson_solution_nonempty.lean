-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_solution_nonempty
-- name    : TheoryOfGames.ThreePerson.solution_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:11.088576+00:00
-- url     : https://prove2.me/theorems/fc3a0556-c935-4ff9-bc27-62ed8eca58d3
-- title:
--   (31:J) — a solution V is never empty
-- statement:
--   Let $v$ be a characteristic function of a zero-sum $n$-person game, satisfying (25:3:a)–(25:3:c), and let $V$ be a solution in the sense of (30:5:a), (30:5:b). Then
--   $$V \neq \ominus .$$
--
--   The statement rests on the existence of at least one imputation, which is where the properties of the characteristic function enter: for a set function admitting no imputation the empty set would satisfy (30:5:a), (30:5:b) vacuously.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 278, 31.2.1, (31:J)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution

namespace TheoryOfGames.ThreePerson

/-- (31:J), 31.2.1: a solution `V` is never empty. -/
theorem solution_nonempty {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : TheoryOfGames.CharFun.IsCharFunction v)
    (V : Set (Fin n → ℝ)) (hV : IsSolution v V) : V.Nonempty := by sorry

end TheoryOfGames.ThreePerson
