-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_isCharFunction_iff_exists_game
-- name    : TheoryOfGames.CharFun.isCharFunction_iff_exists_game
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:54:15.389845+00:00
-- url     : https://prove2.me/theorems/4391c820-4d15-48c5-8165-6f450dde24b4
-- title:
--   26.2 — v is the characteristic function of a zero-sum n-person game iff it satisfies (25:3:a)–(25:3:c)
-- statement:
--   Let $v$ be a numerical set function on the subsets of $I = \{1, \dots, n\}$. Then $v$ is the characteristic function (25.1.3) of some zero-sum $n$-person game $\Gamma$ in normalized form, with finitely many pure strategies for every player, if and only if
--
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \ominus .$$
--
--   This is the complete mathematical characterization of the characteristic functions of all zero-sum $n$-person games, obtained in 25.3–26.1: the "only if" half is 25.3.1 and the "if" half is 26.1.1. It justifies calling every function with these properties a characteristic function, and it is why the analysis of §27 and the later chapters can work with such set functions directly.
--
--   **Formalization Note** Players are `Fin n`, coalitions `Finset (Fin n)`, $-S$ is `Sᶜ`. The characteristic function of a game is `ZeroSumGame.charFun`, in which the coalition's mixed strategy is a single probability vector on its members' strategy tuples. No lower bound on $n$ is assumed.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 245, 26.2; p. 243, 26.1.1; p. 241, 25.3.1

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- 26.2 (with 25.3.1 and 26.1.1): the complete characterization of the characteristic
functions of all zero-sum `n`-person games. A numerical set function `v` on the subsets of
`I = Fin n` is the characteristic function of some zero-sum `n`-person game with finitely many
pure strategies per player if and only if it fulfills (25:3:a)–(25:3:c). -/
theorem isCharFunction_iff_exists_game {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔ ∃ Γ : ZeroSumGame n, Γ.charFun = v := by sorry

end TheoryOfGames.CharFun
