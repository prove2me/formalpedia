-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_mkCollisionNode
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.unique_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:35.770172+00:00
-- url     : https://prove2.me/theorems/32f87bd5-fd10-4830-9d1f-59db93af778a
-- title:
--   Raw: unique mk Collision Node
-- statement:
--   The Raw construction uses the unique mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L219-L225
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L219-L225

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_unique_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.unique_mkCollisionNode {k₁ k₂ : α} (hne : k₁ ≠ k₂) :
    Unique (mkCollisionNode k₁ k₂) := by sorry
