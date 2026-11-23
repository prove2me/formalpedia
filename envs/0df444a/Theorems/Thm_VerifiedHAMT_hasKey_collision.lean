-- Prove2me | Theorems.Thm_VerifiedHAMT_hasKey_collision
-- name    : VerifiedHAMT.hasKey_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:16.347858+00:00
-- url     : https://prove2.me/theorems/9b52f103-2ecf-493a-bf2b-3dd794f1615f
-- title:
--   Verified HAMT: has Key collision
-- statement:
--   The Verified HAMT construction uses the has Key collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L45-L50
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L45-L50

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

theorem VerifiedHAMT.hasKey_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} :
    HasKey key (.collision keys vals hsz) ↔ key ∈ keys := by sorry
