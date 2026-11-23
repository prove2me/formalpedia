-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_empty
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:30.482894+00:00
-- url     : https://prove2.me/theorems/045ba7f9-39b1-454e-afc7-ba7166fdabe8
-- title:
--   Raw: well Formed empty
-- statement:
--   The Raw construction uses the well Formed empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L155-L162
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L155-L162

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_wellFormed_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_empty (hashAt : α → USize) :
    WellFormed hashAt mkEmptyEntries := by sorry
