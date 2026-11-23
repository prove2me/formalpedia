-- Prove2me | Theorems.Thm_VerifiedHAMT_keyList_collision
-- name    : VerifiedHAMT.keyList_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:52.599808+00:00
-- url     : https://prove2.me/theorems/a8946c12-abe2-4f1d-bc9e-c8241c08defb
-- title:
--   Verified HAMT: key List collision
-- statement:
--   The Verified HAMT construction uses the key List collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L59-L61
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L59-L61

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.keyList_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} : keyList (.collision keys vals hsz) = keys.toList := by sorry
