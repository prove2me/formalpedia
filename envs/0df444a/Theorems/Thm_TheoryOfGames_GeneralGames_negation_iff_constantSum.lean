-- Prove2me | Theorems.Thm_TheoryOfGames_GeneralGames_negation_iff_constantSum
-- name    : TheoryOfGames.GeneralGames.negation_iff_constantSum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:36:20.223879+00:00
-- url     : https://prove2.me/theorems/9a425c53-197c-44d7-888c-697e844b148b
-- title:
--   (57:G) — v(−S) = −v(S) iff v(S) + v(−S) = v(I) and v(I) = 0
-- statement:
--   Let $v(S)$, $S \subseteq I = \{1,\dots,n\}$, be a set function satisfying (57:2:a) $v(\emptyset) = 0$ and (57:2:c) $v(S \cup T) \geqq v(S) + v(T)$ for disjoint $S, T$. Write $-S = I - S$. Then the condition
--   $$\text{(57:19)}\quad v(-S) = -v(S) \quad \text{for all } S \subseteq I$$
--   holds if and only if both
--   $$\text{(57:20)}\quad v(S) + v(-S) = v(I) \quad \text{for all } S \subseteq I$$
--   and $v(I) = 0$ hold.
--
--   (57:19) together with (57:2:a), (57:2:c) characterizes the characteristic functions of zero-sum games, and (57:20) those of constant-sum games; the theorem places the former class inside the latter.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 536–537, 57.5.2, (57:19), (57:20), (57:G)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- (57:G), 57.5.2: for a set function `v` on the subsets of `I = (1, …, n)` fulfilling
(57:2:a), (57:2:c), the condition (57:19) `v(-S) = -v(S)` (for all `S ⊆ I`) is equivalent to
the conjunction of (57:20) `v(S) + v(-S) = v(I)` (for all `S ⊆ I`) with `v(I) = 0`. -/
theorem negation_iff_constantSum {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    (∀ S : Finset (Fin n), v Sᶜ = -v S) ↔
      ((∀ S : Finset (Fin n), v S + v Sᶜ = v Finset.univ) ∧ v Finset.univ = 0) := by sorry

end TheoryOfGames.GeneralGames
