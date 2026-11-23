-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_insert
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.valid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:37.389019+00:00
-- url     : https://prove2.me/theorems/0f3a8589-404f-4059-b7b0-a6d8ca6547b3
-- title:
--   Raw: valid insert
-- statement:
--   Insertion preserves the routing invariant even when the input has duplicate keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L150-L155
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L150-L155

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.valid_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    Valid (insert map key) := by sorry
