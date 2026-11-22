-- Prove2me | Theorems.Thm_VanishingOffTsupport
-- name    : VanishingOffTsupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:38.568232+00:00
-- url     : https://prove2.me/theorems/7fa8f6f7-fbd4-4914-8fec-5e58655667a9
-- title:
--   Vanishing Off Tsupport: Vanishing Off Tsupport
-- statement:
--   A real function on the plane and its classical gradient field both vanish off the
--   function's TOPOLOGICAL support.  For the value this is immediate from the definition of
--   `tsupport` as a closure; for the gradient it is not, and the point is that the complement of the
--   closure is OPEN, so off it the function agrees with the zero function on a whole neighbourhood
--   and the gradient of a locally constant function vanishes.  Vanishing off the open support alone
--   would not give the gradient clause.
--
--   Both clauses are stated with their quantifiers INSIDE the conjunction, over all `f` and all `x`,
--   so that the node has no hypotheses and no parameters and a consumer obtains the pair once and
--   applies it to each of its own test functions.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/VanishingOffTsupport.lean#L13-L19
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/VanishingOffTsupport.lean#L13-L19

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_VanishingOffTsupport
set_option autoImplicit false

theorem VanishingOffTsupport :
    (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → f x = 0)
      ∧ (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → gradient f x = 0) := by sorry
