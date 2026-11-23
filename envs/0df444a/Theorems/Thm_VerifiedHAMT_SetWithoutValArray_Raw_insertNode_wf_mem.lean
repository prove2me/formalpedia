-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNode_wf_mem
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertNode_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:37.973426+00:00
-- url     : https://prove2.me/theorems/53ecf9d0-2059-4827-85f9-7b2da4f0eed2
-- title:
--   Raw: insert Node wf mem
-- statement:
--   Insertion preserves routing and membership for the hash at the current offset.
--   The bound keeps the offset arithmetic valid on both 32-bit and 64-bit platforms.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L109-L147
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L109-L147

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertNode_wf_mem [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (key : α) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by sorry
