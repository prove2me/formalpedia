-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_mem_keys
-- name    : VerifiedHAMT.Map.mem_keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:12.210795+00:00
-- url     : https://prove2.me/theorems/45341a39-2f32-4047-96e8-48d515f613e2
-- title:
--   Map: mem keys
-- statement:
--   The Map construction uses the mem keys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L155-L156
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L155-L156

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

theorem VerifiedHAMT.Map.mem_keys (map : Map α β) (key : α) : key ∈ map.keys ↔ key ∈ map := by sorry
