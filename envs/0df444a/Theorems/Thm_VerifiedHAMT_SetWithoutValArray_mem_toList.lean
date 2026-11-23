-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_toList
-- name    : VerifiedHAMT.SetWithoutValArray.mem_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:12:31.151302+00:00
-- url     : https://prove2.me/theorems/101c177b-4654-4bdb-92c6-0ec40700ee89
-- title:
--   Set Without Val Array: mem to List
-- statement:
--   The Set Without Val Array construction uses the mem to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L100-L101
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L100-L101

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.mem_toList (set : SetWithoutValArray α) (key : α) : key ∈ set.toList ↔ key ∈ set := by sorry
