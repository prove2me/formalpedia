-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_dominates_iff
-- name    : TheoryOfGames.ThreePerson.dominates_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:37:03.855857+00:00
-- url     : https://prove2.me/theorems/1942c118-786c-4b1b-9112-04034129b870
-- title:
--   (32:4) — domination in the reduced three-person game
-- statement:
--   Consider the reduced essential zero-sum three-person game (32:1): $v(S) = 0, -1, 1, 0$ when $S$ has $0, 1, 2, 3$ elements. For imputations $\vec\alpha = \{\alpha_1, \alpha_2, \alpha_3\}$ and $\vec\beta = \{\beta_1, \beta_2, \beta_3\}$ of this game, domination $\vec\alpha \succ \vec\beta$ holds if and only if
--
--   $$\text{either } \alpha_1 > \beta_1,\ \alpha_2 > \beta_2; \text{ or } \alpha_1 > \beta_1,\ \alpha_3 > \beta_3; \text{ or } \alpha_2 > \beta_2,\ \alpha_3 > \beta_3 .$$
--
--   Only the two-element coalitions matter for domination in this game; the statement reduces the general definition (30:4) to a condition on coordinates and is the basis of the graphical method of 32.1.
--
--   **Formalization Note** Players $1, 2, 3$ are indices `0, 1, 2`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 284, 32.1.3, (32:4)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

namespace TheoryOfGames.ThreePerson

/-- (32:4), 32.1.3: for imputations `α = {α₁, α₂, α₃}`, `β = {β₁, β₂, β₃}` of the reduced
three-person game (32:1), domination `α ⊱ β` means: either `α₁ > β₁, α₂ > β₂`; or
`α₁ > β₁, α₃ > β₃`; or `α₂ > β₂, α₃ > β₃` (players `1, 2, 3` are `0, 1, 2`). -/
theorem dominates_iff (α β : Fin 3 → ℝ) (hα : IsImputation redV α)
    (hβ : IsImputation redV β) :
    Dominates redV α β ↔
      (β 0 < α 0 ∧ β 1 < α 1) ∨ (β 0 < α 0 ∧ β 2 < α 2) ∨ (β 1 < α 1 ∧ β 2 < α 2) := by sorry

end TheoryOfGames.ThreePerson
