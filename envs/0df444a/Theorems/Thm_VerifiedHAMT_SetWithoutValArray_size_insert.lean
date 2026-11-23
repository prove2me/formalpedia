-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_size_insert
-- name    : VerifiedHAMT.SetWithoutValArray.size_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:55.973805+00:00
-- url     : https://prove2.me/theorems/64b96ef3-e3a8-48af-ba2c-dbc5ff8f736b
-- title:
--   Set Without Val Array: size insert
-- statement:
--   The Set Without Val Array construction uses the size insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L112-L117
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L112-L117

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.size_insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 := by sorry
