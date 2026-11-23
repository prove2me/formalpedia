-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mem_iff_exists_mapsTo
-- name    : VerifiedHAMT.Map.mem_iff_exists_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:01:18.28223+00:00
-- url     : https://prove2.me/theorems/48c58fd3-9908-48a5-b476-a1f8782569ec
-- title:
--   Map: mem iff exists maps To
-- statement:
--   The Map construction uses the mem iff exists maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L165-L167
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L165-L167

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.mem_iff_exists_mapsTo (map : Map α β) (key : α) :
    key ∈ map ↔ ∃ value, map.MapsTo key value := by sorry
