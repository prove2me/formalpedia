-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_set
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:32.098575+00:00
-- url     : https://prove2.me/theorems/91e9424c-22a8-47db-ae6d-6a12dc8052ec
-- title:
--   Raw: well Formed set
-- statement:
--   The Raw construction uses the well Formed set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L183-L191
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L183-L191

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_set {hashAt : α → USize} {es : Array (Entry α (Node α))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by sorry
