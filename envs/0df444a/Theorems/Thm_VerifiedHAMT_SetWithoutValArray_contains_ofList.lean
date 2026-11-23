-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_ofList
-- name    : VerifiedHAMT.SetWithoutValArray.contains_ofList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:57.748442+00:00
-- url     : https://prove2.me/theorems/a3df1d48-90c0-4aa6-b8f7-fcc04c3f771b
-- title:
--   Set Without Val Array: contains of List
-- statement:
--   The Set Without Val Array construction uses the contains of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L151-L154
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L151-L154

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.contains_ofList [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by sorry
