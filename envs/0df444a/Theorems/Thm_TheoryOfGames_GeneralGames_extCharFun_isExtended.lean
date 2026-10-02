-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_extCharFun_isExtended
-- name    : TheoryOfGames.GeneralGames.extCharFun_isExtended
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:23:46.213833+00:00
-- url     : https://prove2.me/theorems/4ea2e32a-d2c9-4262-abd3-da7c11bfad38
-- title:
--   (57:1:a)–(57:1:c) — properties of the extended characteristic function
-- statement:
--   Let $\Gamma$ be a general $n$-person game and let $v(S)$, $S \subseteq \overline I = \{1, \dots, n, n+1\}$, be its extended characteristic function, i.e. the characteristic function of its zero-sum extension $\overline\Gamma$. Then, with $\bot S = \overline I - S$,
--   $$v(\emptyset) = 0, \qquad v(\bot S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset \quad (S, T \subseteq \overline I).$$
--
--   These are the conditions (25:3:a)–(25:3:c) of the zero-sum theory, applied to the zero-sum $(n+1)$-person game $\overline\Gamma$; they are the necessary half of the characterization in 57.3.4.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 528–529, 57.2.1, (57:1:a)–(57:1:c)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.2.1, (57:1:a)–(57:1:c): the extended characteristic function `v(S)`, `S ⊆ Ī`, of every
general `n`-person game `Γ` fulfills (57:1:a) `v(∅) = 0`, (57:1:b) `v(⊥S) = -v(S)` and
(57:1:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`. -/
theorem extCharFun_isExtended {n : ℕ} (Γ : GeneralGame n) :
    IsExtendedCharFunction Γ.extCharFun := by sorry

end TheoryOfGames.GeneralGames
