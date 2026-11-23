-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__insert_cd8cc38688c5
-- name    : P2M_VerifiedHAMT_Map_find__insert_cd8cc38688c5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:30.959023+00:00
-- url     : https://prove2.me/theorems/a1d1fe75-5fcd-4488-8aa2-fc4dd4962ae3
-- title:
--   P2 M Verified HAMT Map find  insert cd8cc38688c5: P2 M Verified HAMT Map find  insert cd8cc38688c5
-- statement:
--   The P2 M Verified HAMT Map find  insert cd8cc38688c5 construction uses the P2 M Verified HAMT Map find  insert cd8cc38688c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L189-L192
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L189-L192

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__insert_cd8cc38688c5 [LawfulBEq α]
    (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).find? q = if q == key then some value else map.find? q := by sorry

alias «VerifiedHAMT».«Map».«find?_insert» := P2M_VerifiedHAMT_Map_find__insert_cd8cc38688c5
