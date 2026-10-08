-- Prove2me | Theorems.Thm_TheoryOfGames_ThreePerson_eq_coord_of_not_dominates
-- name    : TheoryOfGames.ThreePerson.eq_coord_of_not_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:37:22.737989+00:00
-- url     : https://prove2.me/theorems/8a206e6a-9d99-4400-9873-1e7c6d879fb7
-- title:
--   (32:5) — mutually undominated imputations differ along a side of the fundamental triangle
-- statement:
--   In the reduced essential zero-sum three-person game (32:1), let $\vec\alpha, \vec\beta$ be imputations such that neither of $\vec\alpha, \vec\beta$ dominates the other. Then the direction from $\vec\alpha$ to $\vec\beta$ is parallel to one of the sides of the fundamental triangle; in coordinates,
--   $$\alpha_i = \beta_i \quad\text{for some } i \in \{1, 2, 3\}.$$
--
--   Every solution is internally undominated by (30:5:a), so this restricts the shape of any two of its points; the search for all solutions in 32.1.4–32.2.2 starts from it.
--
--   **Formalization Note** The fundamental triangle is the set of imputations $\alpha_1, \alpha_2, \alpha_3 \geqq -1$, $\alpha_1+\alpha_2+\alpha_3 = 0$, with sides on the lines $\alpha_i = -1$; a direction in the plane $\sum_i \alpha_i = 0$ is parallel to the side $\alpha_i = -1$ exactly when its $i$-th coordinate is $0$. The statement is therefore rendered as `∃ i, α i = β i`. For $\vec\alpha = \vec\beta$ the book's direction is undefined and the conclusion holds trivially.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 285, 32.1.3, (32:5)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

namespace TheoryOfGames.ThreePerson

/-- (32:5), 32.1.3: if neither of the imputations `α`, `β` of the reduced three-person game
dominates the other, then the direction from `α` to `β` is parallel to one of the sides of the
fundamental triangle, i.e. `αᵢ = βᵢ` for some player `i`. -/
theorem eq_coord_of_not_dominates (α β : Fin 3 → ℝ) (hα : IsImputation redV α)
    (hβ : IsImputation redV β) (hαβ : ¬ Dominates redV α β) (hβα : ¬ Dominates redV β α) :
    ∃ i : Fin 3, α i = β i := by sorry

end TheoryOfGames.ThreePerson
