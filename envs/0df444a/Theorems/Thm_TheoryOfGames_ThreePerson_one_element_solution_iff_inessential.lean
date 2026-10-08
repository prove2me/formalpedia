-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_one_element_solution_iff_inessential
-- name    : TheoryOfGames.ThreePerson.one_element_solution_iff_inessential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:45.795718+00:00
-- url     : https://prove2.me/theorems/f091d99d-ec84-41a1-bccb-3d4edf6e6585
-- title:
--   (31:P) — a one-element solution exists iff the game is inessential, and then it is the only solution
-- statement:
--   Let $v$ be a characteristic function of a zero-sum $n$-person game, satisfying (25:3:a)–(25:3:c).
--
--   1. The game possesses a one-element solution $V = (\vec\alpha)$ if and only if it is inessential.
--   2. If the game is inessential, then there is an imputation $\vec\alpha$ such that $V = (\vec\alpha)$ is its only solution:
--   $$V \text{ is a solution} \iff V = (\vec\alpha).$$
--
--   This combines (31:N) and (31:O) and answers the first question of 30.4.1: one-element solutions are exactly the inessential case, so every essential game has only solutions with at least two elements.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 280, 31.2.3, (31:N), (31:O), (31:P)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.ThreePerson

/-- (31:P), 31.2.3: a game possesses a one-element solution if and only if it is inessential;
and then it possesses no other solutions. -/
theorem one_element_solution_iff_inessential {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : TheoryOfGames.CharFun.IsCharFunction v) :
    ((∃ α : Fin n → ℝ, IsSolution v {α}) ↔ TheoryOfGames.CharFun.IsInessential v) ∧
    (TheoryOfGames.CharFun.IsInessential v →
      ∃ α : Fin n → ℝ, ∀ V : Set (Fin n → ℝ), IsSolution v V ↔ V = {α}) := by sorry

end TheoryOfGames.ThreePerson
