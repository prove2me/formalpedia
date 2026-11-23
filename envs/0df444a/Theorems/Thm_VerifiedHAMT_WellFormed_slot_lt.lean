-- Prove2me | Theorems.Thm_VerifiedHAMT_WellFormed_slot_lt
-- name    : VerifiedHAMT.WellFormed.slot_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:50.263816+00:00
-- url     : https://prove2.me/theorems/93a482a4-a8eb-4f22-b457-efbf1e6a2634
-- title:
--   Well Formed: slot lt
-- statement:
--   The Well Formed construction uses the slot lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L127-L131
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L127-L131

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.WellFormed.slot_lt {hashAt : α → USize}
    {es : Array (Entry α β (Node α β))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by sorry
