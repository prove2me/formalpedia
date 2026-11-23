-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_eq_true_iff
-- name    : VerifiedHAMT.Set.contains_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:43.841145+00:00
-- url     : https://prove2.me/theorems/aba3a34f-b85c-457f-a924-c78c89bff0d1
-- title:
--   Set: contains eq true iff
-- statement:
--   The Set construction uses the contains eq true iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L94-L95
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L94-L95

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.contains_eq_true_iff [LawfulBEq α] (set : Set α) (key : α) :
    set.contains key = true ↔ key ∈ set := by sorry
