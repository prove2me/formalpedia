-- Prove2me | Theorems.Thm_VerifiedHAMT_hasBinding_entries
-- name    : VerifiedHAMT.hasBinding_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:08.936931+00:00
-- url     : https://prove2.me/theorems/b276eb9b-b5d4-4b0c-aeea-ae842875bfb4
-- title:
--   Verified HAMT: has Binding entries
-- statement:
--   The Verified HAMT construction uses the has Binding entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L187-L201
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L187-L201

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

theorem VerifiedHAMT.hasBinding_entries {es : Array (Entry α β (Node α β))} {key : α} {value : β} :
    HasBinding key value (.entries es) ↔
      ∃ (i : Nat) (hi : i < es.size), EntryHasBinding key value es[i] := by sorry
