-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_nodup_toList
-- name    : VerifiedHAMT.Set.nodup_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:14.946261+00:00
-- url     : https://prove2.me/theorems/8d7e2d37-7d7d-4d24-9637-3eabf2a99896
-- title:
--   Set: nodup to List
-- statement:
--   The Set construction uses the nodup to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L106-L106
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L106-L106

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_nodup_toList

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.nodup_toList (set : Set α) : set.toList.Nodup := by sorry
