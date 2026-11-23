-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.not_mem_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:26.671981+00:00
-- url     : https://prove2.me/theorems/9ec5d20f-3827-451b-9c77-4749c30967c7
-- title:
--   Raw: not mem empty
-- statement:
--   The Raw construction uses the not mem empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L168-L170
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L168-L170

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.not_mem_empty [BEq α] [Hashable α] (key : α) :
    ¬ Mem key (empty : VerifiedHAMT.SetWithoutValArray.Raw α) := by sorry
