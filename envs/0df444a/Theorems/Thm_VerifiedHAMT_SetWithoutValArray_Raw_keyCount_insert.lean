-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyCount_insert
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.keyCount_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:44:44.118915+00:00
-- url     : https://prove2.me/theorems/e3df1f40-045f-48c4-b7e0-cd039d9169be
-- title:
--   Raw: key Count insert
-- statement:
--   The Raw construction uses the key Count insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L138-L163
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L138-L163

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.keyCount_insert [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    keyCount (insert set key).root =
      if contains set key then keyCount set.root else keyCount set.root + 1 := by sorry
