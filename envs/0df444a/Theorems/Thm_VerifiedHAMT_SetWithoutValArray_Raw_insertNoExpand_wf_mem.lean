-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNoExpand_wf_mem
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:59.052188+00:00
-- url     : https://prove2.me/theorems/ec27b926-db13-4d7d-b273-4d6a23b02506
-- title:
--   Raw: insert No Expand wf mem
-- statement:
--   The Raw construction uses the insert No Expand wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L64-L75
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L64-L75

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_wf_mem [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α) :
    letI res := insertNoExpand node (hashAt key) key
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by sorry
