-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_findD_eq_of_mapsTo
-- name    : VerifiedHAMT.Map.findD_eq_of_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:41.568042+00:00
-- url     : https://prove2.me/theorems/ae2cc388-c494-4e10-9b34-02db3ec2e4a1
-- title:
--   Map: find D eq of maps To
-- statement:
--   The Map construction uses the find D eq of maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L142-L145
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L142-L145

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_eq_of_mapsTo

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.findD_eq_of_mapsTo [LawfulBEq α] (map : Map α β)
    (key : α) (value fallback : β) (hb : map.MapsTo key value) :
    map.findD key fallback = value := by sorry
