-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_eq_true_iff
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.containsNode_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:40:17.980511+00:00
-- url     : https://prove2.me/theorems/bc519500-514f-43a7-95d8-80fed67f5bff
-- title:
--   Raw: contains Node eq true iff
-- statement:
--   The Raw construction uses the contains Node eq true iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L106-L109
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L106-L109

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.containsNode_eq_true_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α) :
    containsNode node (hashAt key) key = true ↔ HasKey key node := by sorry
