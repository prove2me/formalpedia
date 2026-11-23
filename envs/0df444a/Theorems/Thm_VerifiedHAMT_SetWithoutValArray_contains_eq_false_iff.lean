-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_eq_false_iff
-- name    : VerifiedHAMT.SetWithoutValArray.contains_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:32.620114+00:00
-- url     : https://prove2.me/theorems/a9bbe8ee-6541-4b18-8073-afe4ef1ed4d4
-- title:
--   Set Without Val Array: contains eq false iff
-- statement:
--   The Set Without Val Array construction uses the contains eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L66-L67
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L66-L67

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_false_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.contains_eq_false_iff [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    set.contains key = false ↔ key ∉ set := by sorry
