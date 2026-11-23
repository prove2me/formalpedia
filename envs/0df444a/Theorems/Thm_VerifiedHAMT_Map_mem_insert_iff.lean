-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mem_insert_iff
-- name    : VerifiedHAMT.Map.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:09.817459+00:00
-- url     : https://prove2.me/theorems/9874ca08-ef05-4ec4-a3d0-70aef417021f
-- title:
--   Map: mem insert iff
-- statement:
--   The Map construction uses the mem insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L232-L234
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L232-L234

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.mem_insert_iff [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    q ∈ map.insert key value ↔ q = key ∨ q ∈ map := by sorry
