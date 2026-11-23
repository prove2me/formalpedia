-- Prove2me | Theorems.Thm_VerifiedHAMT_wellFormed_mkCollisionNode
-- name    : VerifiedHAMT.wellFormed_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:08.004958+00:00
-- url     : https://prove2.me/theorems/0f292a66-5557-4e67-bff7-f594e669cf51
-- title:
--   Verified HAMT: well Formed mk Collision Node
-- statement:
--   The Verified HAMT construction uses the well Formed mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L150-L151
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L150-L151

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

theorem VerifiedHAMT.wellFormed_mkCollisionNode (hashAt : α → USize) (k₁ k₂ : α) (v₁ v₂ : β) :
    WellFormed hashAt (mkCollisionNode k₁ v₁ k₂ v₂) := by sorry
