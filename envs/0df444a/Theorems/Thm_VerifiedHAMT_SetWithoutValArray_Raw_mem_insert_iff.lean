-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:08.829436+00:00
-- url     : https://prove2.me/theorems/a1a6f348-8598-4e36-960b-28789decc949
-- title:
--   Raw: mem insert iff
-- statement:
--   Exact membership update; uniqueness is not needed.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L158-L163
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L158-L163

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.mem_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    Mem q (insert map key) ↔ q = key ∨ Mem q map := by sorry
