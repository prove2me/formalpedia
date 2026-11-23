-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__eq_some_iff_80d7561a98c5
-- name    : P2M_VerifiedHAMT_Map_find__eq_some_iff_80d7561a98c5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:42.894197+00:00
-- url     : https://prove2.me/theorems/e3737059-6097-4bc8-b900-23d65c4d13c4
-- title:
--   P2 M Verified HAMT Map find  eq some iff 80d7561a98c5: P2 M Verified HAMT Map find  eq some iff 80d7561a98c5
-- statement:
--   The P2 M Verified HAMT Map find  eq some iff 80d7561a98c5 construction uses the P2 M Verified HAMT Map find  eq some iff 80d7561a98c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L130-L132
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L130-L132

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__eq_some_iff_80d7561a98c5 [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    map.find? key = some value ↔ map.MapsTo key value := by sorry

alias «VerifiedHAMT».«Map».«find?_eq_some_iff» := P2M_VerifiedHAMT_Map_find__eq_some_iff_80d7561a98c5
