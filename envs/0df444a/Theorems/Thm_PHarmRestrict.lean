-- Prove2me | Theorems.Thm_PHarmRestrict
-- name    : PHarmRestrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:12:19.470814+00:00
-- url     : https://prove2.me/theorems/7505c05b-55f3-4996-9c87-3935e3dd9ecf
-- title:
--   PHarm Restrict: PHarm Restrict
-- statement:
--   Domain restriction and data congruence for `p`-harmonicity.  If `u` is
--   `p`-harmonic on `Ω` with weak gradient `g`, then
--
--   * (a) `u` is `p`-harmonic with the same weak gradient on every open `Ω' ⊆ Ω`, and
--   * (b) `IsPHarm p Ω u g` depends on `u` and `g` only through their restrictions to
--     `Ω`: replacing them by any `u'`, `g'` agreeing with them on `Ω` preserves it.
--
--   Neither is automatic: `IsPHarm` bundles the domain with an explicit weak gradient,
--   so it has no domain functoriality for free.  (a) is what feeds a solution on
--   `ball 0 1` into a statement about `ball 0 (1/2)`; (b) is what licenses extending a
--   limit object defined only on a closed ball by `0` off that ball.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmRestrict.lean#L17-L98
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmRestrict.lean#L17-L98

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_PFluxContinuity
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmRestrict
import Theorems.Thm_PFluxContinuity
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PHarmRestrict (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane) (h : IsPHarm p Ω u g) :
    (∀ Ω' : Set Plane, IsOpen Ω' → Ω' ⊆ Ω → IsPHarm p Ω' u g) ∧
    (∀ (u' : Plane → ℝ) (g' : Plane → Plane),
      Set.EqOn u u' Ω → Set.EqOn g g' Ω → IsPHarm p Ω u' g') := by sorry
