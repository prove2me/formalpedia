-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNode_unique
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertNode_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:44:34.983868+00:00
-- url     : https://prove2.me/theorems/0dd7090b-91a0-4623-ada2-f30e5fafe7b4
-- title:
--   Raw: insert Node unique
-- statement:
--   The Raw construction uses the insert Node unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L90-L123
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L90-L123

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertNode_unique [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (hu : Unique node) (key : α) :
    Unique (insertNode levels offset node ((hash key).toUSize >>> offset) key) := by sorry
