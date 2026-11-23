-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_length_keys
-- name    : VerifiedHAMT.Map.length_keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:11.700731+00:00
-- url     : https://prove2.me/theorems/a2d2dfa4-10e9-498a-a505-8a5c94496c03
-- title:
--   Map: length keys
-- statement:
--   `size` is the number of keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L162-L163
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L162-L163

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

theorem VerifiedHAMT.Map.length_keys (map : Map α β) : map.keys.length = map.size := by sorry
