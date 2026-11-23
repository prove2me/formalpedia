-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_size_insert
-- name    : VerifiedHAMT.Map.size_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:05.960334+00:00
-- url     : https://prove2.me/theorems/9ff54348-0ad5-48c4-b21f-3d19c8d1db95
-- title:
--   Map: size insert
-- statement:
--   The Map construction uses the size insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L217-L222
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L217-L222

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

theorem VerifiedHAMT.Map.size_insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).size = if key ∈ map then map.size else map.size + 1 := by sorry
