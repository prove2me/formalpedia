-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__isSome_eq_contains_0b5aa7778ea5
-- name    : P2M_VerifiedHAMT_Map_find__isSome_eq_contains_0b5aa7778ea5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:33.773169+00:00
-- url     : https://prove2.me/theorems/bee7e947-39bd-4975-a9be-41f9283ce391
-- title:
--   P2 M Verified HAMT Map find  is Some eq contains 0b5aa7778ea5: P2 M Verified HAMT Map find  is Some eq contains 0b5aa7778ea5
-- statement:
--   The P2 M Verified HAMT Map find  is Some eq contains 0b5aa7778ea5 construction uses the P2 M Verified HAMT Map find  is Some eq contains 0b5aa7778ea5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L138-L140
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L138-L140

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__isSome_eq_contains_0b5aa7778ea5 [LawfulBEq α] (map : Map α β) (key : α) :
    (map.find? key).isSome = map.contains key := by sorry

alias «VerifiedHAMT».«Map».«find?_isSome_eq_contains» := P2M_VerifiedHAMT_Map_find__isSome_eq_contains_0b5aa7778ea5
