-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_empty
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.contains_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:17.337377+00:00
-- url     : https://prove2.me/theorems/9e99edf3-3a8a-4c9c-af95-1a7b5bf3748c
-- title:
--   Raw: contains empty
-- statement:
--   The Raw construction uses the contains empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L123-L125
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L123-L125

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.contains_empty [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    contains (empty : Raw α) key = false := by sorry
