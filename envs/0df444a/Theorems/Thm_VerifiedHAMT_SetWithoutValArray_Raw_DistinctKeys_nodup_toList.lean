-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_nodup_toList
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.nodup_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:05.674851+00:00
-- url     : https://prove2.me/theorems/21dd44f4-da87-440d-a43f-0bab5b8fd8b5
-- title:
--   Distinct Keys: nodup to List
-- statement:
--   The Distinct Keys construction uses the nodup to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L84-L90
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L84-L90

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.nodup_toList {keys : Array α} (h : DistinctKeys keys) :
    keys.toList.Nodup := by sorry
