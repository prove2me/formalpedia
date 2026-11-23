-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mapsTo_insert_of_ne
-- name    : VerifiedHAMT.Map.mapsTo_insert_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:58.271668+00:00
-- url     : https://prove2.me/theorems/98ffd718-5cf5-48cd-bab4-850a0d23c5f0
-- title:
--   Map: maps To insert of ne
-- statement:
--   The Map construction uses the maps To insert of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L247-L250
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L247-L250

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_of_ne

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.mapsTo_insert_of_ne [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) (hne : q ≠ key) :
    (map.insert key value).MapsTo q w ↔ map.MapsTo q w := by sorry
