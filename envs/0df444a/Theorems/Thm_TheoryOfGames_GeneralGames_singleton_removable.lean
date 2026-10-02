-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_singleton_removable
-- name    : TheoryOfGames.GeneralGames.singleton_removable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:38:37.961162+00:00
-- url     : https://prove2.me/theorems/fab62c74-5cea-4758-9f62-7f689155df19
-- title:
--   (57:B) — every one-element set is removable in every zero-sum game
-- statement:
--   Let $\Gamma$ be a zero-sum $n$-person game and $k \in I = \{1, \dots, n\}$. Then the one-element set $S = \{k\}$ is **removable** for $\Gamma$ in the sense of (57:A): there is a zero-sum $n$-person game $\Gamma'$, with finitely many pure strategies per player, which has the same characteristic function as $\Gamma$ and in which all payoffs $\mathcal H'_1, \dots, \mathcal H'_n$ are independent of the variable $\tau_k$.
--
--   The book reads this as saying that the role of any single player in a zero-sum game, as far as coalitions and compensations are concerned, can be duplicated exactly by an arrangement in which he has no direct influence on the play.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 533, 57.4.1, (57:A), (57:B)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_Removable

namespace TheoryOfGames.GeneralGames

/-- (57:B), 57.4.1: every one-element set `S = (k)` is removable (in the sense of (57:A)) in
every zero-sum `n`-person game `Γ`. -/
theorem singleton_removable {n : ℕ} (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) (k : Fin n) :
    Γ.IsRemovable {k} := by sorry

end TheoryOfGames.GeneralGames
