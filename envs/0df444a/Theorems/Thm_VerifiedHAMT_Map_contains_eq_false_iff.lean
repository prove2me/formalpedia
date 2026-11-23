-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_contains_eq_false_iff
-- name    : VerifiedHAMT.Map.contains_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:58:30.980157+00:00
-- url     : https://prove2.me/theorems/aa06aade-a1fa-4f1a-9d2a-4ee91661e47a
-- title:
--   Map: contains eq false iff
-- statement:
--   The Map construction uses the contains eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L126-L128
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L126-L128

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.contains_eq_false_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = false ↔ key ∉ map := by sorry
