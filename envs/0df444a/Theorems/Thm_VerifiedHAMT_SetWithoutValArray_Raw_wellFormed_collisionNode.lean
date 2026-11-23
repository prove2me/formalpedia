-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_collisionNode
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_collisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:16.978265+00:00
-- url     : https://prove2.me/theorems/8219b607-2a1a-4717-a82f-aeb85fab7f10
-- title:
--   Raw: well Formed collision Node
-- statement:
--   The Raw construction uses the well Formed collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L175-L179
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L175-L179

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_wellFormed_collisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_collisionNode (hashAt : α → USize) (b : CollisionNode α) :
    WellFormed hashAt b.val := by sorry
