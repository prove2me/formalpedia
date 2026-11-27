-- Prove2me | Theorems.Thm_RamanujanNested_truncRadical_monotone
-- name    : RamanujanNested.truncRadical_monotone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:04:58.875885+00:00
-- url     : https://prove2.me/theorems/b95d2dcd-527e-57dc-a422-fc83103816ab
-- title:
--   Ramanujan Nested: trunc Radical monotone
-- statement:
--   `truncRadical a` is monotone in the truncation depth, for nonnegative
--   coefficients — the monotonicity half of Section 4.1's convergence argument.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Monotone.lean#L49-L53
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Monotone.lean#L49-L53

module
public import Definitions.Def_RamanujanNested_Defs
public import Definitions.Def_RamanujanNested_Monotone
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.truncRadical_monotone (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Monotone (truncRadical a) := by sorry
