-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_findD_eq_of_not_mem
-- name    : VerifiedHAMT.Map.findD_eq_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:57.557609+00:00
-- url     : https://prove2.me/theorems/c768936d-d2ba-4eaf-a212-0d560aaedf1f
-- title:
--   Map: find D eq of not mem
-- statement:
--   The Map construction uses the find D eq of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L147-L149
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L147-L149

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_eq_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.findD_eq_of_not_mem [LawfulBEq α] (map : Map α β)
    (key : α) (fallback : β) (hm : key ∉ map) : map.findD key fallback = fallback := by sorry
