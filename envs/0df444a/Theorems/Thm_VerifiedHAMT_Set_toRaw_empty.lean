-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_toRaw_empty
-- name    : VerifiedHAMT.Set.toRaw_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:56.755806+00:00
-- url     : https://prove2.me/theorems/eb9ebbed-e4b0-4750-a0b4-7da59e608d06
-- title:
--   Set: to Raw empty
-- statement:
--   The Set construction uses the to Raw empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L85-L86
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L85-L86

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.toRaw_empty :
    (∅ : Set α).toRaw = Lean.PersistentHashSet.empty := by sorry
