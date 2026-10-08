-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_never_dominates_self
-- name    : TheoryOfGames.ThreePerson.never_dominates_self
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:23:58.253586+00:00
-- url     : https://prove2.me/theorems/a929bdd4-8bbd-4c81-95ae-8e9469d3762f
-- title:
--   (31:K) — never α ⊱ α
-- statement:
--   Let $v$ be a function on the subsets of the player set $I = \{1, \dots, n\}$ and let $\vec\alpha$ be an imputation for $v$. Then $\vec\alpha$ does not dominate itself:
--   $$\text{never } \vec\alpha \succ \vec\alpha .$$
--
--   Domination is irreflexive; this is used whenever a one-element set is tested as a solution, as in (31:O).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 278, 31.2.2, (31:K)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution

namespace TheoryOfGames.ThreePerson

/-- (31:K), 31.2.2: never `α ⊱ α`. -/
theorem never_dominates_self {n : ℕ} (v : Finset (Fin n) → ℝ) (α : Fin n → ℝ)
    (hα : IsImputation v α) : ¬ Dominates v α α := by sorry

end TheoryOfGames.ThreePerson
