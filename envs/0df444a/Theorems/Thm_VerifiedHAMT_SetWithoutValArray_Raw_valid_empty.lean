-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.valid_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:28.959147+00:00
-- url     : https://prove2.me/theorems/fbf5f7fa-f8e4-4bd3-82dd-152e856bd245
-- title:
--   Raw: valid empty
-- statement:
--   The Raw construction uses the valid empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L164-L166
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L164-L166

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_valid_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.valid_empty [BEq α] [Hashable α] :
    Valid (empty : VerifiedHAMT.SetWithoutValArray.Raw α) := by sorry
