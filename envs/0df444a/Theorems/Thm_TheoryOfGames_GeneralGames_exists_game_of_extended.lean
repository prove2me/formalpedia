-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_exists_game_of_extended
-- name    : TheoryOfGames.GeneralGames.exists_game_of_extended
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:29:25.714035+00:00
-- url     : https://prove2.me/theorems/a0e1159b-0eaa-4c76-9ab9-c5dbbddf5648
-- title:
--   57.3.3 — every set function with (57:1:a)–(57:1:c) is an extended characteristic function
-- statement:
--   Let $v(S)$, $S \subseteq \overline I = \{1,\dots,n,n+1\}$, be a numerical set function satisfying (57:1:a)–(57:1:c): with $\bot S = \overline I - S$,
--   $$v(\emptyset) = 0, \qquad v(\bot S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset .$$
--   Then there exists a general $n$-person game $\Gamma$, with finitely many pure strategies for each player, whose extended characteristic function equals $v(S)$ for every $S \subseteq \overline I$.
--
--   This is the sufficiency half of the characterization of extended characteristic functions in 57.3.4.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 532, 57.3.3, (57:9)–(57:11)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.3: the necessary conditions (57:1:a)–(57:1:c) are also sufficient. For any numerical
set function `v(S)` (`S ⊆ Ī = (1, …, n, n + 1)`) which fulfills (57:1:a)–(57:1:c) there
exists a general `n`-person game `Γ` of which this `v(S)` is the extended characteristic
function. -/
theorem exists_game_of_extended {n : ℕ} (v : Finset (Fin (n + 1)) → ℝ)
    (hv : IsExtendedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.extCharFun = v := by sorry

end TheoryOfGames.GeneralGames
