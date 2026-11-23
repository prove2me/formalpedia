-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_false_iff
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_false_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:32:15.477071+00:00
-- url     : https://prove2.me/theorems/55736e62-1fa2-4310-b7f2-367abc54b349
-- title:
--   Raw: contains eq false iff
-- statement:
--   The Raw construction uses the contains eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L117-L121
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L117-L121

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_false_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains map key = false ↔ ¬ Mem key map := by sorry
