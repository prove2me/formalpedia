-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollision_size_eq
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:27.078912+00:00
-- url     : https://prove2.me/theorems/119e4970-0cc3-4da2-b445-a3024e2a5e82
-- title:
--   Raw: insert Collision size eq
-- statement:
--   The Raw construction uses the insert Collision size eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L132-L136
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L132-L136

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq [BEq α] (keys : Array α) (key : α) :
    (getCollisionNodeSize (insertCollision keys key) == keys.size) = keys.contains key := by sorry
