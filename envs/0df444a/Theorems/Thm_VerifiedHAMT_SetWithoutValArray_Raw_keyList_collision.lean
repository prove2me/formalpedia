-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:51.95698+00:00
-- url     : https://prove2.me/theorems/4129b446-7f3f-4efc-b40e-d27fe04b2b50
-- title:
--   Raw: key List collision
-- statement:
--   The Raw construction uses the key List collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L57-L58
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L57-L58

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision {keys : Array α} : keyList (.collision keys) = keys.toList := by sorry
