-- Prove2me | Theorems.Thm_RamanujanNested_truncRadicalNS_bounded
-- name    : RamanujanNested.truncRadicalNS_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:02:05.353904+00:00
-- url     : https://prove2.me/theorems/315b9450-141c-51c0-963e-d884dbe4d06a
-- title:
--   Ramanujan Nested: trunc Radical NS bounded
-- statement:
--   The Ramanujan Nested construction uses the trunc Radical NS bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L244-L246
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L244-L246

module
public import Mathlib
public import Definitions.Def_RamanujanNested_IdentityChainNthRoot
set_option autoImplicit true
@[expose] public section
open RamanujanNested
open Finset

theorem RamanujanNested.truncRadicalNS_bounded {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) (d : ℕ) :
    1 ≤ truncRadicalNS n N d ∧ truncRadicalNS n N d ≤ N := by sorry
