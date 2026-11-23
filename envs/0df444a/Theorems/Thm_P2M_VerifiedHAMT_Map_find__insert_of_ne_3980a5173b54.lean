-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__insert_of_ne_3980a5173b54
-- name    : P2M_VerifiedHAMT_Map_find__insert_of_ne_3980a5173b54
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:47.234873+00:00
-- url     : https://prove2.me/theorems/1da59ea3-034c-4b23-991d-8ea7dd8f753e
-- title:
--   P2 M Verified HAMT Map find  insert of ne 3980a5173b54: P2 M Verified HAMT Map find  insert of ne 3980a5173b54
-- statement:
--   The P2 M Verified HAMT Map find  insert of ne 3980a5173b54 construction uses the P2 M Verified HAMT Map find  insert of ne 3980a5173b54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L199-L202
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L199-L202

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__insert_of_ne_3980a5173b54 [LawfulBEq α]
    (map : Map α β) (key q : α) (value : β) (hne : q ≠ key) :
    (map.insert key value).find? q = map.find? q := by sorry

alias «VerifiedHAMT».«Map».«find?_insert_of_ne» := P2M_VerifiedHAMT_Map_find__insert_of_ne_3980a5173b54
