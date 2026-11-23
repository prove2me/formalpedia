-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_findD_insert_self
-- name    : VerifiedHAMT.Map.findD_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:46.785888+00:00
-- url     : https://prove2.me/theorems/54ba27f4-ab90-4c2a-bc59-815dfaab42fe
-- title:
--   Map: find D insert self
-- statement:
--   The Map construction uses the find D insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L210-L213
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L210-L213

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.findD_insert_self [LawfulBEq α]
    (map : Map α β) (key : α) (value fallback : β) :
    (map.insert key value).findD key fallback = value := by sorry
