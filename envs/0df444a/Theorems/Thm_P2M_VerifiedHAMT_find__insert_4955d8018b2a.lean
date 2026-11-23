-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a
-- name    : P2M_VerifiedHAMT_find__insert_4955d8018b2a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:52.749966+00:00
-- url     : https://prove2.me/theorems/d57518ce-6e24-4365-b463-ec4e26743857
-- title:
--   P2 M Verified HAMT find  insert 4955d8018b2a: P2 M Verified HAMT find  insert 4955d8018b2a
-- statement:
--   The P2 M Verified HAMT find  insert 4955d8018b2a construction uses the P2 M Verified HAMT find  insert 4955d8018b2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L245-L255
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L245-L255

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

theorem P2M_VerifiedHAMT_find__insert_4955d8018b2a [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) :
    VerifiedHAMT.find? (VerifiedHAMT.insert map key value) q = if q == key then some value else VerifiedHAMT.find? map q := by sorry

alias «VerifiedHAMT».«find?_insert» := P2M_VerifiedHAMT_find__insert_4955d8018b2a
