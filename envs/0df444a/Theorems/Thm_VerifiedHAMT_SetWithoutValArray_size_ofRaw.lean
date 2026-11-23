-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_size_ofRaw
-- name    : VerifiedHAMT.SetWithoutValArray.size_ofRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:07:46.750912+00:00
-- url     : https://prove2.me/theorems/2ef6a88e-af71-428f-9a81-0abc5c5705b5
-- title:
--   Set Without Val Array: size of Raw
-- statement:
--   The Set Without Val Array construction uses the size of Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L86-L88
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L86-L88

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.size_ofRaw (raw : Raw α)
    (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    (ofRaw raw valid unique).size = Raw.keyCount raw.root := by sorry
