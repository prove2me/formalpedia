-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_insert
-- name    : VerifiedHAMT.SetWithoutValArray.toRaw_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:09:18.211803+00:00
-- url     : https://prove2.me/theorems/b0f8f350-60e8-4451-ae1b-0aaf1984dd15
-- title:
--   Set Without Val Array: to Raw insert
-- statement:
--   The Set Without Val Array construction uses the to Raw insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L94-L95
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L94-L95

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.toRaw_insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).toRaw = Raw.insert set.toRaw key := by sorry
