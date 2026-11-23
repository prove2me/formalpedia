-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:58.811386+00:00
-- url     : https://prove2.me/theorems/edda36ef-d4cc-4bdb-be48-4e04ce9d2980
-- title:
--   Raw: contains eq true iff
-- statement:
--   `contains` is exactly structural key membership, assuming the routing invariant.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L112-L115
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L112-L115

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_true_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map := by sorry
