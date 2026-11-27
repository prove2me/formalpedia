-- Prove2me | Theorems.Thm_RamanujanNested_truncRadicalN_monotone
-- name    : RamanujanNested.truncRadicalN_monotone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:09:45.196032+00:00
-- url     : https://prove2.me/theorems/91c8a5c4-ef16-46e2-b355-b0abebe5879c
-- title:
--   Ramanujan Nested: trunc Radical N monotone
-- statement:
--   `rollUpN n a 1` is monotone in the truncation depth, for nonnegative
--   coefficients — the monotonicity half for general root order `n`.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L179-L183
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L179-L183

module
public import Definitions.Def_RamanujanNested_Defs
public import Mathlib
public import Definitions.Def_RamanujanNested_NthRootChain
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.truncRadicalN_monotone (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Monotone (fun N => rollUpN n a 1 N) := by sorry
