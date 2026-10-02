-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_charFun_isCharFunction
-- name    : TheoryOfGames.CharFun.charFun_isCharFunction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T03:45:20.58799+00:00
-- url     : https://prove2.me/theorems/3c28c1eb-3b4c-47dd-b5a3-c299231ff415
-- title:
--   25.3.1 — the characteristic function of every zero-sum n-person game satisfies (25:3:a)–(25:3:c)
-- statement:
--   Let $\Gamma$ be a zero-sum $n$-person game in normalized form (finitely many pure strategies $\beta_k \geqq 1$ for each player $k$, real payoffs $\mathcal H_k$ with $\sum_k \mathcal H_k \equiv 0$), and let $v(S)$ be its characteristic function (25.1.3): the value $\operatorname{Max}_\xi \operatorname{Min}_\eta K(\xi,\eta)$ of the two-person game between the coalition $S$ and its complement $-S$, the coalition mixing jointly over its members' strategy tuples. Then $v$ fulfills
--
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \ominus,$$
--
--   that is, (25:3:a)–(25:3:c), for all subsets $S, T$ of $I = \{1, \dots, n\}$.
--
--   This is the "only if" half of the characterization of characteristic functions in 26.2.
--
--   **Formalization Note** Players are `Fin n`, coalitions `Finset (Fin n)`, $-S$ is `Sᶜ`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 241, 25.3.1, (25:3:a)–(25:3:c)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- 25.3.1: the characteristic function `v(S)` of every zero-sum `n`-person game fulfills
(25:3:a) `v(∅) = 0`, (25:3:b) `v(-S) = -v(S)` and (25:3:c) `v(S ∪ T) ≥ v(S) + v(T)` if
`S ∩ T = ∅`. -/
theorem charFun_isCharFunction {n : ℕ} (Γ : ZeroSumGame n) :
    IsCharFunction Γ.charFun := by sorry

end TheoryOfGames.CharFun
