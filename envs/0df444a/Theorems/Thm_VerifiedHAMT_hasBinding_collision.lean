-- Prove2me | Theorems.Thm_VerifiedHAMT_hasBinding_collision
-- name    : VerifiedHAMT.hasBinding_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:20.605237+00:00
-- url     : https://prove2.me/theorems/1e1d4edb-c4da-485a-986b-7a82bbefd595
-- title:
--   Verified HAMT: has Binding collision
-- statement:
--   The Verified HAMT construction uses the has Binding collision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L179-L185
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L179-L185

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

theorem VerifiedHAMT.hasBinding_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} {value : β} :
    HasBinding key value (.collision keys vals hsz) ↔
      ∃ (i : Nat) (hi : i < keys.size), keys[i] = key ∧ vals[i]'(hsz ▸ hi) = value := by sorry
