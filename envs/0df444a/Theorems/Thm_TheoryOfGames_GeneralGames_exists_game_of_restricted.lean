-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_exists_game_of_restricted
-- name    : TheoryOfGames.GeneralGames.exists_game_of_restricted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:27:54.954201+00:00
-- url     : https://prove2.me/theorems/651ed171-bd61-4aed-a6f4-8f89afe0e312
-- title:
--   57.3.1 — every set function with (57:2:a), (57:2:c) is a restricted characteristic function
-- statement:
--   Let $v(S)$, $S \subseteq I = \{1,\dots,n\}$, be a numerical set function satisfying
--   $$\text{(57:2:a)}\ v(\emptyset) = 0, \qquad \text{(57:2:c)}\ v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset .$$
--   Then there exists a general $n$-person game $\Gamma$, with finitely many pure strategies for each player, whose restricted characteristic function equals $v(S)$ for every $S \subseteq I$.
--
--   This is the sufficiency half of the characterization of restricted characteristic functions in 57.3.4.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 530, 57.3.1; proof pp. 530–532, 57.3.1–57.3.2, (57:3)–(57:8)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.1: the necessary conditions (57:2:a), (57:2:c) are also sufficient. For any numerical
set function `v(S)` (`S ⊆ I`) which fulfills (57:2:a), (57:2:c) there exists a general
`n`-person game `Γ` (finitely many pure strategies per player) of which this `v(S)` is the
restricted characteristic function. -/
theorem exists_game_of_restricted {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v := by sorry

end TheoryOfGames.GeneralGames
