-- Prove2me | Theorems.Thm_VerifiedHAMT_unique_mkCollisionNode
-- name    : VerifiedHAMT.unique_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:15.036715+00:00
-- url     : https://prove2.me/theorems/765083d9-73aa-4c30-9ab6-fc837d014751
-- title:
--   Verified HAMT: unique mk Collision Node
-- statement:
--   The Verified HAMT construction uses the unique mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L308-L314
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L308-L314

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

theorem VerifiedHAMT.unique_mkCollisionNode {k₁ k₂ : α} (hne : k₁ ≠ k₂) (v₁ v₂ : β) :
    Unique (mkCollisionNode k₁ v₁ k₂ v₂) := by sorry
