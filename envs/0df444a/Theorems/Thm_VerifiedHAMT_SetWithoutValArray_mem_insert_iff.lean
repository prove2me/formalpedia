-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_insert_iff
-- name    : VerifiedHAMT.SetWithoutValArray.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:07:09.913794+00:00
-- url     : https://prove2.me/theorems/e6595f58-ec00-4938-8435-d3e70449d8e2
-- title:
--   Set Without Val Array: mem insert iff
-- statement:
--   The Set Without Val Array construction uses the mem insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L129-L130
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L129-L130

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.mem_insert_iff [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := by sorry
