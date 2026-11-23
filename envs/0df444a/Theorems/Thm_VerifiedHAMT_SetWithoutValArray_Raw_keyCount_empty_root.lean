-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyCount_empty_root
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.keyCount_empty_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:40:27.832181+00:00
-- url     : https://prove2.me/theorems/137c4cfa-d434-4277-bf7b-1e7f550c9af7
-- title:
--   Raw: key Count empty root
-- statement:
--   The Raw construction uses the key Count empty root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L163-L166
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L163-L166

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.keyCount_empty_root [BEq α] [Hashable α] :
    keyCount (empty : Raw α).root = 0 := by sorry
