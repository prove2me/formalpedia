-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_size_insert
-- name    : VerifiedHAMT.Set.size_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:41.608524+00:00
-- url     : https://prove2.me/theorems/d9217294-e576-42ff-8371-4384727ebb48
-- title:
--   Set: size insert
-- statement:
--   The Set construction uses the size insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L114-L116
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L114-L116

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_size_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.size_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 := by sorry
