-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_insert
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.unique_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:45.445455+00:00
-- url     : https://prove2.me/theorems/1e27475d-a64a-436a-b995-165bf00af633
-- title:
--   Raw: unique insert
-- statement:
--   The Raw construction uses the unique insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L125-L131
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L125-L131

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.unique_insert [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    Unique (insert set key).root := by sorry
