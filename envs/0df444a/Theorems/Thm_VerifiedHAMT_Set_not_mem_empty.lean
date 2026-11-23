-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_not_mem_empty
-- name    : VerifiedHAMT.Set.not_mem_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:04.574545+00:00
-- url     : https://prove2.me/theorems/7c449516-26f7-43f4-b8de-13ade2a0671c
-- title:
--   Set: not mem empty
-- statement:
--   The Set construction uses the not mem empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L100-L101
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L100-L101

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.not_mem_empty (key : α) : key ∉ (∅ : Set α) := by sorry
