-- Prove2me | Theorems.Thm_VerifiedHAMT_findD_empty
-- name    : VerifiedHAMT.findD_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:34:11.569205+00:00
-- url     : https://prove2.me/theorems/5153b201-972e-4fba-aa0d-02b2ca7028ad
-- title:
--   Verified HAMT: find D empty
-- statement:
--   The Verified HAMT construction uses the find D empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L282-L285
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L282-L285

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findD_empty [BEq α] [LawfulBEq α] [Hashable α]
    (key : α) (fallback : β) :
    findD (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key fallback = fallback := by sorry
