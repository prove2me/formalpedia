-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__insert_self_b790a82edd3e
-- name    : P2M_VerifiedHAMT_Map_find__insert_self_b790a82edd3e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:44.848794+00:00
-- url     : https://prove2.me/theorems/3a9f1690-aede-4a80-8ef3-0e7b0a48dee5
-- title:
--   P2 M Verified HAMT Map find  insert self b790a82edd3e: P2 M Verified HAMT Map find  insert self b790a82edd3e
-- statement:
--   The P2 M Verified HAMT Map find  insert self b790a82edd3e construction uses the P2 M Verified HAMT Map find  insert self b790a82edd3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L194-L197
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L194-L197

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__insert_self_b790a82edd3e [LawfulBEq α]
    (map : Map α β) (key : α) (value : β) :
    (map.insert key value).find? key = some value := by sorry

alias «VerifiedHAMT».«Map».«find?_insert_self» := P2M_VerifiedHAMT_Map_find__insert_self_b790a82edd3e
