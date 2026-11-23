-- Prove2me | Theorems.Thm_VerifiedHAMT_DistinctKeys_push
-- name    : VerifiedHAMT.DistinctKeys.push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:36.055342+00:00
-- url     : https://prove2.me/theorems/c1a8f06d-3905-468a-8921-81b04c4546d4
-- title:
--   Distinct Keys: push
-- statement:
--   The Distinct Keys construction uses the push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L262-L264
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L262-L264

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

theorem VerifiedHAMT.DistinctKeys.push {keys : Array α} (hu : DistinctKeys keys)
    {key : α} (fresh : key ∉ keys) : DistinctKeys (keys.push key) := by sorry
