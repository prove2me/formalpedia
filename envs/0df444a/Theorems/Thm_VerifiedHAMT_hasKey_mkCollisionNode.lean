-- Prove2me | Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
-- name    : VerifiedHAMT.hasKey_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:18.542232+00:00
-- url     : https://prove2.me/theorems/86f76ea8-5a11-4553-afde-9725f3fdb5c6
-- title:
--   Verified HAMT: has Key mk Collision Node
-- statement:
--   The Verified HAMT construction uses the has Key mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L76-L78
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L76-L78

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

theorem VerifiedHAMT.hasKey_mkCollisionNode (k₁ k₂ q : α) (v₁ v₂ : β) :
    HasKey q (mkCollisionNode k₁ v₁ k₂ v₂) ↔ q = k₁ ∨ q = k₂ := by sorry
