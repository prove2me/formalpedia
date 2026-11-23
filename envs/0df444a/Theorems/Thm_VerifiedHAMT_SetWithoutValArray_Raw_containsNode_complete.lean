-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_complete
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.containsNode_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:58.00106+00:00
-- url     : https://prove2.me/theorems/c2a879b0-aa01-4e21-b742-0d1c7b0f4690
-- title:
--   Raw: contains Node complete
-- statement:
--   On a well-formed node, hash-directed traversal finds every stored key.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L93-L104
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L93-L104

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.containsNode_complete [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : containsNode node (hashAt key) key = true := by sorry
