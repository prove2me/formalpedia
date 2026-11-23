-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_findD_insert
-- name    : VerifiedHAMT.Map.findD_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:02:55.203338+00:00
-- url     : https://prove2.me/theorems/905fc806-6374-4a45-9c88-ff72fbea092e
-- title:
--   Map: find D insert
-- statement:
--   The Map construction uses the find D insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L204-L208
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L204-L208

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.findD_insert [LawfulBEq α]
    (map : Map α β) (key q : α) (value fallback : β) :
    (map.insert key value).findD q fallback =
      if q == key then value else map.findD q fallback := by sorry
