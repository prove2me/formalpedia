-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_toRaw_insert
-- name    : VerifiedHAMT.Map.toRaw_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:22.95668+00:00
-- url     : https://prove2.me/theorems/593cb5a0-5a55-4270-a751-58504a1b8eb3
-- title:
--   Map: to Raw insert
-- statement:
--   The Map construction uses the to Raw insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L119-L120
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L119-L120

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

theorem VerifiedHAMT.Map.toRaw_insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).toRaw = VerifiedHAMT.insert map.toRaw key value := by sorry
