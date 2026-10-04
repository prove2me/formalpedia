-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_chess_trichotomy
-- name    : TheoryOfGames.PerfectInfo.chess_trichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:03:13.754016+00:00
-- url     : https://prove2.me/theorems/158f1ba6-1cb7-4058-bbc0-bdd9f7c133f7
-- title:
--   (15:13), (15:D:a)–(15:D:c) — in a Chess-like game one player can force a win, or both can force a tie
-- statement:
--   Let $\Gamma$ be a finite zero-sum two-person game with perfect information that contains **no chance moves** and in which every play has outcome $1$, $0$ or $-1$ for player 1 ("win", "tie", "loss"; as in Chess). Let $v = v_1 = \operatorname{Max}_{\tau_1}\operatorname{Min}_{\tau_2}\mathcal H(\tau_1, \tau_2)$ (which equals $v_2$ by (15:13)). Then $v$ is one of $1, 0, -1$, and:
--
--   1. **(15:D:a)** if $v = 1$, player 1 ("white") has a strategy $\tau_1$ with $\mathcal H(\tau_1, \tau_2) = 1$ for every strategy $\tau_2$ of player 2: he wins irrespective of what player 2 does;
--   2. **(15:D:b)** if $v = 0$, player 1 has a strategy $\tau_1$ with $\mathcal H(\tau_1, \tau_2) \geqq 0$ for every $\tau_2$, and player 2 has a strategy $\tau_2$ with $\mathcal H(\tau_1, \tau_2) \leqq 0$ for every $\tau_1$: each can tie (and possibly win) irrespective of the other;
--   3. **(15:D:c)** if $v = -1$, player 2 ("black") has a strategy $\tau_2$ with $\mathcal H(\tau_1, \tau_2) = -1$ for every $\tau_1$.
--
--   Footnote 3 on p. 125 explains why the sharp trichotomy fails in general when there are chance moves; the hypothesis "no chance moves" is essential.
--
--   **Formalization Note** Without chance moves $\mathcal H(\tau_1, \tau_2)$ is the payoff of the single play the two strategies produce, so "wins" means $\mathcal H = 1$ for player 1 and $\mathcal H = -1$ for player 2, and "ties or wins" means $\mathcal H \geqq 0$ for player 1 and $\mathcal H \leqq 0$ for player 2.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 125, 15.7.1, (15:13), (15:D:a)–(15:D:c), footnotes 1–3

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values
import Definitions.Def_TheoryOfGames_PerfectInfo_ChessLike

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:13), (15:D:a)–(15:D:c): in a game with perfect information, without chance moves, whose
plays have outcomes `1, 0, -1` for player 1, the value `v = v₁` is one of `1, 0, -1`, and
(a) if `v = 1` player 1 has a strategy that wins against every strategy of player 2;
(b) if `v = 0` each player has a strategy that at least ties against every strategy of the other;
(c) if `v = -1` player 2 has a strategy that wins against every strategy of player 1. -/
theorem chess_trichotomy (t : GameTree) (hnc : NoChanceMoves t)
    (hout : OutcomesWinTieLoss t) :
    (v1 t = 1 ∨ v1 t = 0 ∨ v1 t = -1) ∧
      (v1 t = 1 → ∃ τ₁ : Strategy1 t, ∀ τ₂ : Strategy2 t, payoff t τ₁ τ₂ = 1) ∧
      (v1 t = 0 → (∃ τ₁ : Strategy1 t, ∀ τ₂ : Strategy2 t, 0 ≤ payoff t τ₁ τ₂) ∧
        (∃ τ₂ : Strategy2 t, ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ ≤ 0)) ∧
      (v1 t = -1 → ∃ τ₂ : Strategy2 t, ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ = -1) := by sorry

end TheoryOfGames.PerfectInfo
