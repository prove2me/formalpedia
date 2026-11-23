-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_size
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:45:58.112899+00:00
-- url     : https://prove2.me/theorems/7bcf788f-805d-4247-a870-54c527d98704
-- title:
--   Raw: insert Collision Aux size
-- statement:
--   The Raw construction uses the insert Collision Aux size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L104-L130
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L104-L130

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_size [BEq α] (keys : Array α) (i : Nat) (key : α) :
    getCollisionNodeSize (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key) =
      if (keys.drop i).contains key then keys.size else keys.size + 1 := by sorry
