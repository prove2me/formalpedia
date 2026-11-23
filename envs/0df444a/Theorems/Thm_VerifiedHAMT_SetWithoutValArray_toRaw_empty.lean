-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_empty
-- name    : VerifiedHAMT.SetWithoutValArray.toRaw_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:08:23.516873+00:00
-- url     : https://prove2.me/theorems/fafed41f-44ea-4a0d-80e9-b22db52fdac7
-- title:
--   Set Without Val Array: to Raw empty
-- statement:
--   The Set Without Val Array construction uses the to Raw empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L92-L92
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L92-L92

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.toRaw_empty : (∅ : SetWithoutValArray α).toRaw = Raw.empty := by sorry
