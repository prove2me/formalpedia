-- Prove2me | Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
-- name    : VerifiedHAMT.HasBinding.hasKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:18.15332+00:00
-- url     : https://prove2.me/theorems/92f750b0-fb89-44fb-83b9-912bd36d8e30
-- title:
--   Has Binding: has Key
-- statement:
--   The Has Binding construction uses the has Key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L203-L208
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L203-L208

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

theorem VerifiedHAMT.HasBinding.hasKey {key : α} {value : β} {node : Node α β}
    (hb : HasBinding key value node) : HasKey key node := by sorry
