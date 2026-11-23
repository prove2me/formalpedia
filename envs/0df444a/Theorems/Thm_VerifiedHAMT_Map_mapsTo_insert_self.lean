-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mapsTo_insert_self
-- name    : VerifiedHAMT.Map.mapsTo_insert_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:02:53.127984+00:00
-- url     : https://prove2.me/theorems/6d316ff8-78bf-48a1-bd07-3cb01c7928de
-- title:
--   Map: maps To insert self
-- statement:
--   The Map construction uses the maps To insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L242-L245
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L242-L245

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.mapsTo_insert_self [LawfulBEq α]
    (map : Map α β) (key : α) (value w : β) :
    (map.insert key value).MapsTo key w ↔ w = value := by sorry
