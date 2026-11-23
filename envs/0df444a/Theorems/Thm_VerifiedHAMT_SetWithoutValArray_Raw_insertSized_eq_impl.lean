-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSized_eq_impl
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertSized_eq_impl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:49:40.136541+00:00
-- url     : https://prove2.me/theorems/058ab547-c139-4434-a4e1-aa49e1ee395d
-- title:
--   Raw: insert Sized eq impl
-- statement:
--   The Raw construction uses the insert Sized eq impl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L201-L203
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L201-L203

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertSized_eq_impl : @insertSized = @insertSizedImpl := by sorry
