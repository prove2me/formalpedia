-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_length_toList
-- name    : VerifiedHAMT.SetWithoutValArray.length_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:36.860731+00:00
-- url     : https://prove2.me/theorems/adceaf26-6f44-4857-97b7-1cf71a3916ac
-- title:
--   Set Without Val Array: length to List
-- statement:
--   The cached count is exactly the number of distinct stored keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L107-L108
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L107-L108

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.length_toList (set : SetWithoutValArray α) : set.toList.length = set.size := by sorry
