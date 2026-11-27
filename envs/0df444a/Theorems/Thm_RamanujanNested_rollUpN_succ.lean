-- Prove2me | Theorems.Thm_RamanujanNested_rollUpN_succ
-- name    : RamanujanNested.rollUpN_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:09:20.033892+00:00
-- url     : https://prove2.me/theorems/f8bef7f9-c294-589e-afe4-b2091ac73384
-- title:
--   Ramanujan Nested: roll Up N succ
-- statement:
--   The Ramanujan Nested construction uses the roll Up N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L54-L56
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L54-L56

module
public import Definitions.Def_RamanujanNested_Defs
public import Mathlib
public import Definitions.Def_RamanujanNested_NthRootChain
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.rollUpN_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    rollUpN n a T (k + 1) =
      (1 + a 1 * rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ)) := by sorry
