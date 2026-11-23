-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_mkCollisionNode
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_mkCollisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:07.543721+00:00
-- url     : https://prove2.me/theorems/89dbbfb7-c439-49da-94ff-979ea6f1777e
-- title:
--   Raw: well Formed mk Collision Node
-- statement:
--   The Raw construction uses the well Formed mk Collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L172-L173
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L172-L173

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_wellFormed_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_mkCollisionNode (hashAt : α → USize) (k₁ k₂ : α) :
    WellFormed hashAt (mkCollisionNode k₁ k₂) := by sorry
