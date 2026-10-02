-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_intervalMap_properties
-- name    : TheoryOfGames.Utility.intervalMap_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T01:13:49.447836+00:00
-- url     : https://prove2.me/theorems/688fdc5a-0485-44b4-b905-9de3a9b6a68f
-- title:
--   (A:E) — properties of $f_{u_0,v_0}$: monotone, and linear toward either endpoint
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), fix $u_0 < v_0$, and let $f = f_{u_0,v_0}$ be the function of (A:D) on the interval $u_0 \leqq w \leqq v_0$. Then, for utilities in that interval:
--
--   1. **(i')** $f$ is monotone: $w < w'$ implies $f(w) < f(w')$;
--   2. **(ii')** for $0 < \beta < 1$ and $w \neq u_0$,
--   $$f\big((1-\beta)u_0 + \beta w\big) = \beta f(w);$$
--   3. **(iii')** for $0 < \beta < 1$ and $w \neq v_0$,
--   $$f\big((1-\beta)v_0 + \beta w\big) = 1 - \beta + \beta f(w).$$
--
--   These properties say that $f$ is the correct numerical scale on the interval: combinations with either endpoint are carried into the corresponding numerical combinations.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 620, (A:E)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_intervalMap

namespace TheoryOfGames.Utility

/-- (A:E): for fixed `u₀ < v₀` the function `f = f_{u₀,v₀}` of (A:D), on the interval
`u₀ ≦ w ≦ v₀`, is (i') monotone, and satisfies
(ii') `f((1 − β)u₀ + βw) = βf(w)` for `0 < β < 1` and `w ≠ u₀`,
(iii') `f((1 − β)v₀ + βw) = 1 − β + βf(w)` for `0 < β < 1` and `w ≠ v₀`. -/
theorem intervalMap_properties {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    (∀ w w' : U, S.le u₀ w → S.le w v₀ → S.le u₀ w' → S.le w' v₀ → S.lt w w' →
        intervalMap S u₀ v₀ w < intervalMap S u₀ v₀ w') ∧
      (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ u₀ →
        intervalMap S u₀ v₀ (S.cmb β u₀ w) = (β : ℝ) * intervalMap S u₀ v₀ w) ∧
      ∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ v₀ →
        intervalMap S u₀ v₀ (S.cmb β v₀ w) = 1 - (β : ℝ) + (β : ℝ) * intervalMap S u₀ v₀ w := by sorry

end TheoryOfGames.Utility
