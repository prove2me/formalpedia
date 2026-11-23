-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
-- name    : P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:33:53.168282+00:00
-- url     : https://prove2.me/theorems/21256555-cd19-47cb-9c76-9f481e09f123
-- title:
--   P2 M Verified HAMT find  insert self b1de16f2743e: P2 M Verified HAMT find  insert self b1de16f2743e
-- statement:
--   The P2 M Verified HAMT find  insert self b1de16f2743e construction uses the P2 M Verified HAMT find  insert self b1de16f2743e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L257-L261
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L257-L261

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

theorem P2M_VerifiedHAMT_find__insert_self_b1de16f2743e [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : VerifiedHAMT.find? (VerifiedHAMT.insert map key value) key = some value := by sorry

alias «VerifiedHAMT».«find?_insert_self» := P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
