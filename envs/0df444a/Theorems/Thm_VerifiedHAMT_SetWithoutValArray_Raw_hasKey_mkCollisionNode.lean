-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:29.633152+00:00
-- url     : https://prove2.me/theorems/f407c2f1-dce3-4f9f-85cc-a80ef45a625f
-- title:
--   Raw: has Key mk Collision Node
-- statement:
--   The Raw construction uses the has Key mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L119-L121
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L119-L121

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode (k₁ k₂ q : α) :
    HasKey q (mkCollisionNode k₁ k₂) ↔ q = k₁ ∨ q = k₂ := by sorry
