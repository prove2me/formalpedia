-- Prove2me | Theorems.Thm_VerifiedHAMT_unique_set
-- name    : VerifiedHAMT.unique_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:57.015248+00:00
-- url     : https://prove2.me/theorems/13ce4c18-fa4c-49cc-a539-ab68a76d7f83
-- title:
--   Verified HAMT: unique set
-- statement:
--   The Verified HAMT construction uses the unique set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L31-L36
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L31-L36

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Bindings
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.unique_set {es : Array (Entry α β (Node α β))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by sorry
