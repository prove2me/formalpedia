-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_nodup_toList
-- name    : VerifiedHAMT.SetWithoutValArray.nodup_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:35.777577+00:00
-- url     : https://prove2.me/theorems/427f1c5c-6c9c-40cc-8c32-ca1f98938ba8
-- title:
--   Set Without Val Array: nodup to List
-- statement:
--   The Set Without Val Array construction uses the nodup to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L103-L104
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L103-L104

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_nodup_toList

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.nodup_toList (set : SetWithoutValArray α) : set.toList.Nodup := by sorry
