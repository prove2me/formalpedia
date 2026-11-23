-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363
-- name    : P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:36:27.032795+00:00
-- url     : https://prove2.me/theorems/807d2f39-6672-4341-847b-5f4d235c3f08
-- title:
--   P2 M Verified HAMT find  insert of ne f04aac250363: P2 M Verified HAMT find  insert of ne f04aac250363
-- statement:
--   The P2 M Verified HAMT find  insert of ne f04aac250363 construction uses the P2 M Verified HAMT find  insert of ne f04aac250363 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L263-L268
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L263-L268

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

theorem P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363 [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) (hne : q ≠ key) :
    VerifiedHAMT.find? (VerifiedHAMT.insert map key value) q = VerifiedHAMT.find? map q := by sorry

alias «VerifiedHAMT».«find?_insert_of_ne» := P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363
