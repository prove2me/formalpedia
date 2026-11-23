-- Prove2me | Theorems.Thm_VerifiedHAMT_contains_empty
-- name    : VerifiedHAMT.contains_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:36.591356+00:00
-- url     : https://prove2.me/theorems/df569fb9-dc3c-4e5f-b8c1-206ab48c38cc
-- title:
--   Verified HAMT: contains empty
-- statement:
--   The Verified HAMT construction uses the contains empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L126-L128
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L126-L128

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.contains_empty [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    contains (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = false := by sorry
