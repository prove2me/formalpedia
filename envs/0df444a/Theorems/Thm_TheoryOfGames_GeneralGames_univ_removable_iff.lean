-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_univ_removable_iff
-- name    : TheoryOfGames.GeneralGames.univ_removable_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:41:02.274543+00:00
-- url     : https://prove2.me/theorems/14d678fa-9f55-41d1-8e45-f4dad7a6777f
-- title:
--   (57:C) — the set of all players is removable iff the game is inessential
-- statement:
--   Let $\Gamma$ be a zero-sum $n$-person game with characteristic function $v(S)$, $S \subseteq I = \{1,\dots,n\}$. Then the set $S = I$ is **removable** for $\Gamma$ in the sense of (57:A) (there is a zero-sum $n$-person game $\Gamma'$ with the same characteristic function in which no player has an influence on the payoffs) if and only if $\Gamma$ is **inessential**, i.e. there are constants $\alpha_1, \dots, \alpha_n$ with
--   $$v(S) = \sum_{k \in S} \alpha_k \qquad \text{for all } S \subseteq I .$$
--
--   Together with (57:B) it shows that the players of an essential game are removable individually but not all simultaneously.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 534, 57.4.2, (57:C), (57:12), (57:13)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_Removable

namespace TheoryOfGames.GeneralGames

/-- (57:C), 57.4.2: for a zero-sum `n`-person game `Γ`, the set `S = I = (1, …, n)` is
removable (in the sense of (57:A)) if and only if the game `Γ` is inessential. -/
theorem univ_removable_iff {n : ℕ} (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) :
    Γ.IsRemovable Finset.univ ↔ IsInessential Γ.restrictedCharFun := by sorry

end TheoryOfGames.GeneralGames
