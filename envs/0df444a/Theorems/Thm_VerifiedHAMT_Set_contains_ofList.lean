-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_ofList
-- name    : VerifiedHAMT.Set.contains_ofList
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:03:38.596174+00:00
-- url     : https://prove2.me/theorems/c0ab3a82-074d-4744-9cc7-bfd4791ef154
-- title:
--   Set: contains of List
-- statement:
--   The Set construction uses the contains of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L152-L155
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L152-L155

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

theorem VerifiedHAMT.Set.contains_ofList [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by sorry
