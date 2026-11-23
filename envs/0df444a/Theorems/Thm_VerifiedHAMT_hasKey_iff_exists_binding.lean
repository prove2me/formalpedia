-- Prove2me | Theorems.Thm_VerifiedHAMT_hasKey_iff_exists_binding
-- name    : VerifiedHAMT.hasKey_iff_exists_binding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:39.391053+00:00
-- url     : https://prove2.me/theorems/064715ae-3dcc-48be-85c4-2a8ea720d55c
-- title:
--   Verified HAMT: has Key iff exists binding
-- statement:
--   The Verified HAMT construction uses the has Key iff exists binding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L217-L227
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L217-L227

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

theorem VerifiedHAMT.hasKey_iff_exists_binding {key : α} {node : Node α β} :
    HasKey key node ↔ ∃ value, HasBinding key value node := by sorry
