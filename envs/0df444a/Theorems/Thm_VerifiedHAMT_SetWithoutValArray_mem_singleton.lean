-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_singleton
-- name    : VerifiedHAMT.SetWithoutValArray.mem_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:23.414273+00:00
-- url     : https://prove2.me/theorems/06b62b22-0b52-46de-b416-bf15960ba0ea
-- title:
--   Set Without Val Array: mem singleton
-- statement:
--   The Set Without Val Array construction uses the mem singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L135-L138
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L135-L138

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.mem_singleton [LawfulBEq α] (key q : α) :
    q ∈ ({key} : SetWithoutValArray α) ↔ q = key := by sorry
