-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_entries
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.keyList_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:19.205819+00:00
-- url     : https://prove2.me/theorems/2b3b4d76-e0b9-462d-b537-eb54e6d5ca4b
-- title:
--   Raw: key List entries
-- statement:
--   The Raw construction uses the key List entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L52-L55
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L52-L55

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.keyList_entries (es : Array (Entry α (Node α))) :
    keyList (.entries es) = es.toList.flatMap entryKeyList := by sorry
