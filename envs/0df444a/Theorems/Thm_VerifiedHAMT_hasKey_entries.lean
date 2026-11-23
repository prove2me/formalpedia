-- Prove2me | Theorems.Thm_VerifiedHAMT_hasKey_entries
-- name    : VerifiedHAMT.hasKey_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:18.951349+00:00
-- url     : https://prove2.me/theorems/a686c20c-4a60-4393-bf0a-e350dfc58bc9
-- title:
--   Verified HAMT: has Key entries
-- statement:
--   The Verified HAMT construction uses the has Key entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L52-L67
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L52-L67

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

theorem VerifiedHAMT.hasKey_entries {es : Array (Entry α β (Node α β))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by sorry
