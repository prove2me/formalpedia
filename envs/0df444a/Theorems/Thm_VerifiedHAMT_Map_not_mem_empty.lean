-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_not_mem_empty
-- name    : VerifiedHAMT.Map.not_mem_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:02.717011+00:00
-- url     : https://prove2.me/theorems/cf1efa7e-2b2f-46b4-be8a-bfa2a1487059
-- title:
--   Map: not mem empty
-- statement:
--   The Map construction uses the not mem empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L173-L174
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L173-L174

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.not_mem_empty (key : α) : key ∉ (∅ : Map α β) := by sorry
