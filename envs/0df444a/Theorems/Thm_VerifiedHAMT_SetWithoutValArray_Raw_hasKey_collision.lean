-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:26.337804+00:00
-- url     : https://prove2.me/theorems/db6e3142-b756-4673-96f9-5621b6d68b69
-- title:
--   Raw: has Key collision
-- statement:
--   The Raw construction uses the has Key collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L89-L93
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L89-L93

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision {keys : Array α} {key : α} :
    HasKey key (.collision keys) ↔ key ∈ keys := by sorry
