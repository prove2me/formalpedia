-- Prove2me | Theorems.Thm_VerifiedHAMT_hasBinding_mkCollisionNode
-- name    : VerifiedHAMT.hasBinding_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:34.943904+00:00
-- url     : https://prove2.me/theorems/230680e8-c166-4ac1-8cec-cb075a6c9976
-- title:
--   Verified HAMT: has Binding mk Collision Node
-- statement:
--   The Verified HAMT construction uses the has Binding mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L229-L237
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L229-L237

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

theorem VerifiedHAMT.hasBinding_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ w : β) :
    HasBinding q w (mkCollisionNode k₁ v₁ k₂ v₂) ↔
      (q = k₁ ∧ w = v₁) ∨ (q = k₂ ∧ w = v₂) := by sorry
