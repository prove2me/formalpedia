-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
-- name    : P2M_VerifiedHAMT_find__empty_a79d102e4768
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:48.381934+00:00
-- url     : https://prove2.me/theorems/aff37075-a55b-4340-aab1-797303e108be
-- title:
--   P2 M Verified HAMT find  empty a79d102e4768: P2 M Verified HAMT find  empty a79d102e4768
-- statement:
--   The P2 M Verified HAMT find  empty a79d102e4768 construction uses the P2 M Verified HAMT find  empty a79d102e4768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L241-L243
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L241-L243

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem P2M_VerifiedHAMT_find__empty_a79d102e4768 [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    VerifiedHAMT.find? (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = none := by sorry

alias «VerifiedHAMT».«find?_empty» := P2M_VerifiedHAMT_find__empty_a79d102e4768
