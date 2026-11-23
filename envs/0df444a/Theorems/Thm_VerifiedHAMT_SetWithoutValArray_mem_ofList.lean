-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_ofList
-- name    : VerifiedHAMT.SetWithoutValArray.mem_ofList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:32.082902+00:00
-- url     : https://prove2.me/theorems/858bf6d5-2601-4f1b-9e14-57f41ee6a420
-- title:
--   Set Without Val Array: mem of List
-- statement:
--   The Set Without Val Array construction uses the mem of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L148-L149
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L148-L149

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.mem_ofList [LawfulBEq α] (keys : List α) (key : α) :
    key ∈ ofList keys ↔ key ∈ keys := by sorry
