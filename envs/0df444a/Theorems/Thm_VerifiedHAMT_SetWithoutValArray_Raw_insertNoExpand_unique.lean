-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNoExpand_unique
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:44:26.92645+00:00
-- url     : https://prove2.me/theorems/251f6687-65b4-4eea-8c25-24448b994ac8
-- title:
--   Raw: insert No Expand unique
-- statement:
--   The Raw construction uses the insert No Expand unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L49-L60
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L49-L60

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_unique [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) :
    Unique (insertNoExpand node (hashAt key) key) := by sorry
