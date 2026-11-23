-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedNoExpand_eq
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertSizedNoExpand_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:46:02.371667+00:00
-- url     : https://prove2.me/theorems/e9e9f845-c50d-45ef-be1b-f0857e427829
-- title:
--   Raw: insert Sized No Expand eq
-- statement:
--   The Raw construction uses the insert Sized No Expand eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L154-L173
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L154-L173

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertSizedNoExpand_eq [BEq α] [Hashable α] (s : SizedRaw α) (h : USize)
    (key : α) :
    insertSizedNoExpand s h key =
      ⟨⟨insertNoExpand s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by sorry
