-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_mem_insert_iff
-- name    : VerifiedHAMT.Set.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:49.980839+00:00
-- url     : https://prove2.me/theorems/a7889f6b-67aa-4a04-bfd2-496512ce691d
-- title:
--   Set: mem insert iff
-- statement:
--   The Set construction uses the mem insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L128-L129
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L128-L129

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.mem_insert_iff [LawfulBEq α] (set : Set α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := by sorry
