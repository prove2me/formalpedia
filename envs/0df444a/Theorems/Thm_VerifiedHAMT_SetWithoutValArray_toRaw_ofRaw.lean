-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_ofRaw
-- name    : VerifiedHAMT.SetWithoutValArray.toRaw_ofRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:07:07.316709+00:00
-- url     : https://prove2.me/theorems/1bc02387-de3e-4d71-87de-490b30875047
-- title:
--   Set Without Val Array: to Raw of Raw
-- statement:
--   The Set Without Val Array construction uses the to Raw of Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L72-L74
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean#L72-L74

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.SetWithoutValArray.toRaw_ofRaw (raw : Raw α)
    (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := by sorry
