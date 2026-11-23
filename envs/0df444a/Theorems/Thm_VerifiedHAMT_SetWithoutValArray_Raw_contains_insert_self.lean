-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert_self
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.contains_insert_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:43:23.466348+00:00
-- url     : https://prove2.me/theorems/c089209d-612b-4945-8db2-38b44945d288
-- title:
--   Raw: contains insert self
-- statement:
--   The Raw construction uses the contains insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L173-L176
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L173-L176

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.contains_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains (insert map key) key = true := by sorry
