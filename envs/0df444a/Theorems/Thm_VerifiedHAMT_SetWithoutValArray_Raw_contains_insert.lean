-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.contains_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:15.550581+00:00
-- url     : https://prove2.me/theorems/be2111a3-a1e7-4730-94b7-c0a7762a53ed
-- title:
--   Raw: contains insert
-- statement:
--   The previously proved lookup composes with the verified insertion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L166-L171
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L166-L171

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.contains_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    contains (insert map key) q = ((q == key) || contains map q) := by sorry
