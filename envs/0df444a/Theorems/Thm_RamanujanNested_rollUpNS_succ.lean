-- Prove2me | Theorems.Thm_RamanujanNested_rollUpNS_succ
-- name    : RamanujanNested.rollUpNS_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:06:44.984495+00:00
-- url     : https://prove2.me/theorems/3571cebd-5275-4749-9bf0-650218eebb85
-- title:
--   Ramanujan Nested: roll Up NS succ
-- statement:
--   The Ramanujan Nested construction uses the roll Up NS succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L182-L184
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L182-L184

module
public import Mathlib
public import Definitions.Def_RamanujanNested_IdentityChainNthRoot
set_option autoImplicit true
@[expose] public section
open RamanujanNested
open Finset

theorem RamanujanNested.rollUpNS_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    rollUpNS n a T (k + 1) =
      ((-1 : ℝ) ^ n + a 1 * rollUpNS n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ)) := by sorry
