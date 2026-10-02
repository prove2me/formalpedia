-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_intervalMap_unique
-- name    : TheoryOfGames.Utility.intervalMap_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T01:16:43.156404+00:00
-- url     : https://prove2.me/theorems/88bed82e-7f0a-44e3-87af-2f6cec87d720
-- title:
--   (A:F) — $f_{u_0,v_0}$ is determined by (i), (ii) and either (ii') or (iii')
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C) and fix $u_0 < v_0$. Let $f_1$ be a mapping of all $w$ with $u_0 \leqq w \leqq v_0$ to real numbers such that $f_1(u_0) = 0$, $f_1(v_0) = 1$, and either
--
--   1. $f_1\big((1-\beta)u_0 + \beta w\big) = \beta f_1(w)$ for all $0 < \beta < 1$ and all $w \neq u_0$ in the interval, or
--   2. $f_1\big((1-\beta)v_0 + \beta w\big) = 1 - \beta + \beta f_1(w)$ for all $0 < \beta < 1$ and all $w \neq v_0$ in the interval.
--
--   Then $f_1$ coincides with the function $f_{u_0,v_0}$ of (A:D):
--   $$f_1(w) = f_{u_0,v_0}(w) \qquad (u_0 \leqq w \leqq v_0).$$
--
--   This is the uniqueness counterpart of (A:E); it is the tool by which the local scales on different intervals are later fitted together.
--
--   **Formalization Note** $f_1$ is a function on all of $U$, but its hypotheses and the conclusion only involve its values on $u_0 \leqq w \leqq v_0$, so this is the book's statement about mappings of the interval.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 620, (A:F)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_intervalMap

namespace TheoryOfGames.Utility

/-- (A:F): for fixed `u₀ < v₀`, a mapping of the `w` with `u₀ ≦ w ≦ v₀` to numbers which
satisfies (i) `f₁(u₀) = 0`, (ii) `f₁(v₀) = 1`, and either (ii') or (iii') of (A:E), coincides
on `u₀ ≦ w ≦ v₀` with the function `f_{u₀,v₀}` of (A:D). -/
theorem intervalMap_unique {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) (f₁ : U → ℝ) (h0 : f₁ u₀ = 0) (h1 : f₁ v₀ = 1)
    (hf : (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ u₀ →
            f₁ (S.cmb β u₀ w) = (β : ℝ) * f₁ w) ∨
          (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ v₀ →
            f₁ (S.cmb β v₀ w) = 1 - (β : ℝ) + (β : ℝ) * f₁ w)) :
    ∀ w : U, S.le u₀ w → S.le w v₀ → f₁ w = intervalMap S u₀ v₀ w := by sorry

end TheoryOfGames.Utility
