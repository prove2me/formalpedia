-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_sound
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.containsNode_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:52.086689+00:00
-- url     : https://prove2.me/theorems/b2ac483c-618b-4229-8c5d-70e573e3b4e2
-- title:
--   Raw: contains Node sound
-- statement:
--   A successful query cannot invent a key, even in a malformed node.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L63-L90
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L63-L90

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.containsNode_sound [BEq α] [LawfulBEq α] (node : Node α)
    (hash : USize) (key : α) (found : containsNode node hash key = true) :
    HasKey key node := by sorry
