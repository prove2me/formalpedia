-- Prove2me | Theorems.Thm_VerifiedHAMT_insertNode_wf_mem
-- name    : VerifiedHAMT.insertNode_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:33.770802+00:00
-- url     : https://prove2.me/theorems/e4312df6-0ac6-4066-bd16-1fde705e9fff
-- title:
--   Verified HAMT: insert Node wf mem
-- statement:
--   Insertion preserves routing and membership for the hash at the current offset.
--   The bound keeps the offset arithmetic valid on both 32-bit and 64-bit platforms.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L184-L222
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L184-L222

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertNode_wf_mem [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α β) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by sorry
