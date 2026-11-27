-- Prove2me | Theorems.Thm_RamanujanNested_rollUp_bounded
-- name    : RamanujanNested.rollUp_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:20.321232+00:00
-- url     : https://prove2.me/theorems/bcc0ef98-b5b4-5958-937a-75b6dfe77ffc
-- title:
--   Ramanujan Nested: roll Up bounded
-- statement:
--   **Section 4.1, boundedness.** For any depth `d` and any coefficient function
--   `a` satisfying `a k ≤ A` pointwise, and any seed `T ∈ [0, r*]`, the truncated
--   radical `rollUp a T d` stays in `[0, r*]`. (See the file docstring for why no
--   lower bound on `a` is needed here.)
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Bounds.lean#L37-L59
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Bounds.lean#L37-L59

module
public import Definitions.Def_RamanujanNested_Defs
public import Definitions.Def_RamanujanNested_Bounds
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.rollUp_bounded {A T : ℝ} (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hTA : T ≤ rStar A) :
    ∀ (d : ℕ) (a : ℕ → ℝ), (∀ k, a k ≤ A) →
      0 ≤ rollUp a T d ∧ rollUp a T d ≤ rStar A := by sorry
