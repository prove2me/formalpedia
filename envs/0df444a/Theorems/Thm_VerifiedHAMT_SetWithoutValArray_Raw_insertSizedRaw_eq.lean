-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedRaw_eq
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertSizedRaw_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:46:33.094318+00:00
-- url     : https://prove2.me/theorems/99843180-8ac6-49ec-bcbc-594eb4ce2c89
-- title:
--   Raw: insert Sized Raw eq
-- statement:
--   The Raw construction uses the insert Sized Raw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L175-L192
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L175-L192

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertSizedRaw_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α) (h : USize) (key : α) :
    insertSizedRaw levels offset s h key =
      ⟨⟨insertNode levels offset s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by sorry
