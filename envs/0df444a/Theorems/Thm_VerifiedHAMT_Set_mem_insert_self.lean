-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_mem_insert_self
-- name    : VerifiedHAMT.Set.mem_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:27.084253+00:00
-- url     : https://prove2.me/theorems/2b5ee718-8f6e-4229-9785-5e9ad8f2c546
-- title:
--   Set: mem insert self
-- statement:
--   The Set construction uses the mem insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L131-L132
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L131-L132

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.mem_insert_self [LawfulBEq α] (set : Set α) (key : α) :
    key ∈ set.insert key := by sorry
