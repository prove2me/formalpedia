-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_WellFormed_slot_lt
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.WellFormed.slot_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:02.21538+00:00
-- url     : https://prove2.me/theorems/9dff92ce-c758-40b2-ad93-168cadf5c3f9
-- title:
--   Well Formed: slot lt
-- statement:
--   The Well Formed construction uses the slot lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L149-L153
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L149-L153

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_WellFormed_slot_lt

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.WellFormed.slot_lt {hashAt : α → USize}
    {es : Array (Entry α (Node α))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by sorry
