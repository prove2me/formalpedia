-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_ofRaw_toRaw
-- name    : VerifiedHAMT.SetWithoutValArray.ofRaw_toRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:07:44.138013+00:00
-- url     : https://prove2.me/theorems/cd01a198-a691-4101-b342-601a1265bd1e
-- title:
--   Set Without Val Array: of Raw to Raw
-- statement:
--   The Set Without Val Array construction uses the of Raw to Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L76-L84
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L76-L84

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.ofRaw_toRaw (set : SetWithoutValArray α) :
    ofRaw set.toRaw set.valid set.unique = set := by sorry
