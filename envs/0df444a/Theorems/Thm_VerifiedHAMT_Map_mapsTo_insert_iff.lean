-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mapsTo_insert_iff
-- name    : VerifiedHAMT.Map.mapsTo_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:51.992104+00:00
-- url     : https://prove2.me/theorems/746bce0c-e2da-4473-b288-f116fc580c55
-- title:
--   Map: maps To insert iff
-- statement:
--   The Map construction uses the maps To insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L236-L240
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L236-L240

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.mapsTo_insert_iff [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) :
    (map.insert key value).MapsTo q w ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ map.MapsTo q w) := by sorry
