-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_contains_insert_self
-- name    : VerifiedHAMT.Map.contains_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:08.838955+00:00
-- url     : https://prove2.me/theorems/8c893ce8-aff6-467c-8646-5296c792d98c
-- title:
--   Map: contains insert self
-- statement:
--   The Map construction uses the contains insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L228-L230
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L228-L230

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.contains_insert_self [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).contains key = true := by sorry
