-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_nodup_keys
-- name    : VerifiedHAMT.Map.nodup_keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:11.159899+00:00
-- url     : https://prove2.me/theorems/65944a55-d15c-49aa-a0d9-1497ba6f89ac
-- title:
--   Map: nodup keys
-- statement:
--   The Map construction uses the nodup keys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L158-L159
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L158-L159

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

theorem VerifiedHAMT.Map.nodup_keys (map : Map α β) : map.keys.Nodup := by sorry
