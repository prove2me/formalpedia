-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_set
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.unique_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:37.363295+00:00
-- url     : https://prove2.me/theorems/525cd4db-2a2d-4c23-92c2-7ceb8dec69a1
-- title:
--   Raw: unique set
-- statement:
--   The Raw construction uses the unique set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L227-L232
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L227-L232

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.unique_set {es : Array (Entry α (Node α))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by sorry
