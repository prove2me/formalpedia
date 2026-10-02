-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_characterization
-- name    : TheoryOfGames.GeneralGames.characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T05:31:52.507816+00:00
-- url     : https://prove2.me/theorems/86a53d43-76df-476f-aade-ccd733ce1deb
-- title:
--   57.3.4 — complete characterization of the restricted and extended characteristic functions
-- statement:
--   Let $n \geqq 0$, $I = \{1,\dots,n\}$ and $\overline I = \{1, \dots, n, n+1\}$.
--
--   1. A numerical set function $v(S)$, $S \subseteq I$, is the restricted characteristic function of some general $n$-person game $\Gamma$ (finitely many pure strategies per player, arbitrary real payoffs) if and only if
--   $$\text{(57:2:a)}\ v(\emptyset) = 0, \qquad \text{(57:2:c)}\ v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset .$$
--   2. A numerical set function $v(S)$, $S \subseteq \overline I$, is the extended characteristic function of some general $n$-person game $\Gamma$ if and only if it satisfies (57:1:a)–(57:1:c):
--   $$v(\emptyset) = 0, \qquad v(\bot S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset ,$$
--   where $\bot S = \overline I - S$.
--
--   In each case one game realizes $v$ on all sets simultaneously. The restricted characteristic functions of general games are thus exactly the superadditive set functions vanishing on $\emptyset$, with $v(I)$ unrestricted; this is the domain on which the theory of general games in Chapter XI is built.
--
--   **Formalization Note** $I$ is `Fin n` and $\overline I$ is `Fin (n + 1)` with the fictitious player `Fin.last n`. The statement is made for every $n$, including $n = 0$, where it still holds.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 532, 57.3.4; with 57.2.1 (pp. 528–529), 57.3.1 (p. 530), 57.3.3 (p. 532)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.4 (with 57.2.1, 57.3.1–57.3.3): the complete mathematical characterizations of both
the restricted and the extended characteristic functions of all possible general `n`-person
games `Γ`. A numerical set function `v` on the subsets of `I = (1, …, n)` is the restricted
characteristic function of some general `n`-person game iff it fulfills (57:2:a), (57:2:c);
a numerical set function on the subsets of `Ī = (1, …, n, n + 1)` is the extended
characteristic function of some general `n`-person game iff it fulfills (57:1:a)–(57:1:c). -/
theorem characterization (n : ℕ) :
    (∀ v : Finset (Fin n) → ℝ,
        IsRestrictedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v) ∧
      (∀ v : Finset (Fin (n + 1)) → ℝ,
        IsExtendedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.extCharFun = v) := by sorry

end TheoryOfGames.GeneralGames
