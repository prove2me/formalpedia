-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_eq_false_iff
-- name    : VerifiedHAMT.Set.contains_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:12.394293+00:00
-- url     : https://prove2.me/theorems/42c7a9ae-3e82-4450-9ded-f769cf49ea34
-- title:
--   Set: contains eq false iff
-- statement:
--   The Set construction uses the contains eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L97-L98
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L97-L98

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_eq_false_iff
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.contains_eq_false_iff [LawfulBEq α] (set : Set α) (key : α) :
    set.contains key = false ↔ key ∉ set := by sorry
