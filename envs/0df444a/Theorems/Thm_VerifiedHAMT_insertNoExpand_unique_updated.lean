-- Prove2me | Theorems.Thm_VerifiedHAMT_insertNoExpand_unique_updated
-- name    : VerifiedHAMT.insertNoExpand_unique_updated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:23.08456+00:00
-- url     : https://prove2.me/theorems/a229c422-74f8-4af0-8bfd-b0c6a9d3ecab
-- title:
--   Verified HAMT: insert No Expand unique updated
-- statement:
--   The Verified HAMT construction uses the insert No Expand unique updated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L137-L150
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L137-L150

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertNoExpand_unique_updated [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    Unique res ∧ Updated node res key value := by sorry
