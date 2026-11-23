-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_empty
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.unique_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:04.91881+00:00
-- url     : https://prove2.me/theorems/ed3e4b82-9a0f-45d0-81b8-603689407759
-- title:
--   Raw: unique empty
-- statement:
--   The Raw construction uses the unique empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L214-L217
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L214-L217

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_unique_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.unique_empty : Unique (mkEmptyEntries : Node α) := by sorry
