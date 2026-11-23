-- Prove2me | Theorems.Thm_VerifiedHAMT_collision_push_binding
-- name    : VerifiedHAMT.collision_push_binding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:47.228276+00:00
-- url     : https://prove2.me/theorems/9c30ce67-2efd-401d-b22e-a4bb7c72b8f1
-- title:
--   Verified HAMT: collision push binding
-- statement:
--   The Verified HAMT construction uses the collision push binding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L239-L247
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L239-L247

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

theorem VerifiedHAMT.collision_push_binding (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size) (key q : α) (value w : β) :
    HasBinding q w (.collision (keys.push key) (vals.push value) (by simp [hsz])) ↔
      (q = key ∧ w = value) ∨ HasBinding q w (.collision keys vals hsz) := by sorry
