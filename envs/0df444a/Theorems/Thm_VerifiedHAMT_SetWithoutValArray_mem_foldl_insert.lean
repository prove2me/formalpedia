-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_foldl_insert
-- name    : VerifiedHAMT.SetWithoutValArray.mem_foldl_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:26.084189+00:00
-- url     : https://prove2.me/theorems/3439ebd0-1b58-4db8-92a9-81751d4b7f66
-- title:
--   Set Without Val Array: mem foldl insert
-- statement:
--   The Set Without Val Array construction uses the mem foldl insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L140-L146
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L140-L146

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.mem_foldl_insert [LawfulBEq α] (keys : List α) (set : SetWithoutValArray α) (q : α) :
    q ∈ keys.foldl insert set ↔ q ∈ set ∨ q ∈ keys := by sorry
