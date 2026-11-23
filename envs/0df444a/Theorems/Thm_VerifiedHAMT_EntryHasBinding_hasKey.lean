-- Prove2me | Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
-- name    : VerifiedHAMT.EntryHasBinding.hasKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:30.07057+00:00
-- url     : https://prove2.me/theorems/667998c6-06dd-4142-98c1-8e31f374c8ee
-- title:
--   Entry Has Binding: has Key
-- statement:
--   The Entry Has Binding construction uses the has Key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L210-L215
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L210-L215

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

theorem VerifiedHAMT.EntryHasBinding.hasKey {q : α} {w : β} {e : Entry α β (Node α β)}
    (h : EntryHasBinding q w e) : EntryHasKey q e := by sorry
