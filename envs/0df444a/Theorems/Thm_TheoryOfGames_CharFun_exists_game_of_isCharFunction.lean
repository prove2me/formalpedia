-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_exists_game_of_isCharFunction
-- name    : TheoryOfGames.CharFun.exists_game_of_isCharFunction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:51:15.823956+00:00
-- url     : https://prove2.me/theorems/c47b9614-76d5-46e2-ba6e-00e861a6afb2
-- title:
--   26.1.1 — every v satisfying (25:3:a)–(25:3:c) is the characteristic function of a zero-sum n-person game
-- statement:
--   Let $v$ be a numerical set function on the subsets of $I = \{1, \dots, n\}$ which fulfills (25:3:a)–(25:3:c):
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \ominus.$$
--   Then there exists a zero-sum $n$-person game $\Gamma$ in normalized form, with finitely many pure strategies for every player, whose characteristic function (25.1.3) equals $v(S)$ for every subset $S$ of $I$.
--
--   This is the converse of 25.3.1: one single game realizes $v$ on all coalitions simultaneously.
--
--   **Formalization Note** Players are `Fin n`; the game is a `ZeroSumGame n` (strategy sets `Fin (β k)` with $\beta_k \geqq 1$, real payoffs summing to zero), and the conclusion is equality of functions on `Finset (Fin n)`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 243, 26.1.1; pp. 243–245, 26.1.1–26.1.2, (26:5)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- 26.1.1: the converse of 25.3.1. For any numerical set function `v(S)` which fulfills the
conditions (25:3:a)–(25:3:c) there exists a zero-sum `n`-person game `Γ` (finitely many pure
strategies per player) of which this `v(S)` is the characteristic function, i.e. whose
characteristic function agrees with `v` on every subset `S` of `I`. -/
theorem exists_game_of_isCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) : ∃ Γ : ZeroSumGame n, Γ.charFun = v := by sorry

end TheoryOfGames.CharFun
