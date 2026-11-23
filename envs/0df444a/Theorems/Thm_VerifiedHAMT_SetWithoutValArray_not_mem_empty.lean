-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_not_mem_empty
-- name    : VerifiedHAMT.SetWithoutValArray.not_mem_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:09:16.763801+00:00
-- url     : https://prove2.me/theorems/4dc9a87b-2046-46b3-9b2c-49a5d3e81f6f
-- title:
--   Set Without Val Array: not mem empty
-- statement:
--   The Set Without Val Array construction uses the not mem empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L97-L98
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L97-L98

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.not_mem_empty (key : α) : key ∉ (∅ : SetWithoutValArray α) := by sorry
