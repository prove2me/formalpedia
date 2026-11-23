-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_insert
-- name    : VerifiedHAMT.SetWithoutValArray.contains_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:09:16.490443+00:00
-- url     : https://prove2.me/theorems/186fdc55-4e26-4996-88b0-3203e4c535eb
-- title:
--   Set Without Val Array: contains insert
-- statement:
--   The Set Without Val Array construction uses the contains insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L122-L124
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L122-L124

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.contains_insert [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) := by sorry
