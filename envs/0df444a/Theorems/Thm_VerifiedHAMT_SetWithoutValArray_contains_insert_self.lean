-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_insert_self
-- name    : VerifiedHAMT.SetWithoutValArray.contains_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:09:14.734863+00:00
-- url     : https://prove2.me/theorems/960376a8-29ac-467e-9bdf-e22729913240
-- title:
--   Set Without Val Array: contains insert self
-- statement:
--   The Set Without Val Array construction uses the contains insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L126-L127
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L126-L127

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.contains_insert_self [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).contains key = true := by sorry
