-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_restrictedCharFun_properties
-- name    : TheoryOfGames.GeneralGames.restrictedCharFun_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:26:04.933013+00:00
-- url     : https://prove2.me/theorems/57dc936f-8d85-4abf-92fb-8cbf9130973a
-- title:
--   (57:2:a), (57:2:c), (57:2:b) — properties of the restricted characteristic function
-- statement:
--   Let $\Gamma$ be a general $n$-person game and let $v(S)$, $S \subseteq I = \{1, \dots, n\}$, be its restricted characteristic function. Write $-S = I - S$. Then:
--
--   1. (57:2:a) $v(\emptyset) = 0$;
--   2. (57:2:c) $v(S \cup T) \geqq v(S) + v(T)$ whenever $S \cap T = \emptyset$;
--   3. (57:2:b) for every $S \subseteq I$,
--   $$v(-S) \leqq v(I) - v(S).$$
--
--   Unlike the zero-sum case, $v(-S) = -v(S)$ need not hold, and $v(I)$ need not be $0$. These are the necessary conditions whose sufficiency is 57.3.1.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 529, 57.2.1, (57:2:a), (57:2:c), (57:2:b)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.2.1, (57:2:a), (57:2:c), (57:2:b): the restricted characteristic function `v(S)`,
`S ⊆ I`, of every general `n`-person game `Γ` fulfills (57:2:a) `v(∅) = 0` and (57:2:c)
`v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`, and also (57:2:b) `v(-S) ≤ v(I) - v(S)`, where
`-S = I - S`. -/
theorem restrictedCharFun_properties {n : ℕ} (Γ : GeneralGame n) :
    IsRestrictedCharFunction Γ.restrictedCharFun ∧
      ∀ S : Finset (Fin n),
        Γ.restrictedCharFun Sᶜ ≤ Γ.restrictedCharFun Finset.univ - Γ.restrictedCharFun S := by sorry

end TheoryOfGames.GeneralGames
