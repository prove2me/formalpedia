-- Prove2me | Theorems.Thm_VerifiedHAMT_findNode_eq_some_iff
-- name    : VerifiedHAMT.findNode_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:56.525376+00:00
-- url     : https://prove2.me/theorems/690dcc92-da9a-47f7-8e9b-79c4013e3f58
-- title:
--   Verified HAMT: find Node eq some iff
-- statement:
--   The Verified HAMT construction uses the find Node eq some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L193-L202
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L193-L202

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

theorem VerifiedHAMT.findNode_eq_some_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node)
    (key : α) (value : β) :
    findNode node (hashAt key) key = some value ↔ HasBinding key value node := by sorry
