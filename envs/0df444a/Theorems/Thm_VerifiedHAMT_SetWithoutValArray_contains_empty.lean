-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_empty
-- name    : VerifiedHAMT.SetWithoutValArray.contains_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:09:20.007653+00:00
-- url     : https://prove2.me/theorems/f9ad4767-e902-40d8-ad0d-9336bdd1f4fd
-- title:
--   Set Without Val Array: contains empty
-- statement:
--   The Set Without Val Array construction uses the contains empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L119-L120
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L119-L120

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.contains_empty [LawfulBEq α] (key : α) :
    (∅ : SetWithoutValArray α).contains key = false := by sorry
