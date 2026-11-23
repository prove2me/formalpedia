-- Prove2me | Theorems.Thm_VerifiedHAMT_hasKey_set_iff
-- name    : VerifiedHAMT.hasKey_set_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:01.205606+00:00
-- url     : https://prove2.me/theorems/74fc3a95-0a26-4120-b0fa-6dc7ddbfd61b
-- title:
--   Verified HAMT: has Key set iff
-- statement:
--   The Verified HAMT construction uses the has Key set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L69-L74
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L69-L74

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

theorem VerifiedHAMT.hasKey_set_iff {es : Array (Entry α β (Node α β))}
    (i : Nat) (hi : i < es.size) (e : Entry α β (Node α β)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by sorry
