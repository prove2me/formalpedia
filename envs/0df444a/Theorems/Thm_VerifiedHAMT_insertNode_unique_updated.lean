-- Prove2me | Theorems.Thm_VerifiedHAMT_insertNode_unique_updated
-- name    : VerifiedHAMT.insertNode_unique_updated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:35:17.379828+00:00
-- url     : https://prove2.me/theorems/70bfa968-bdc2-4a0e-9763-6eb16709f897
-- title:
--   Verified HAMT: insert Node unique updated
-- statement:
--   The Verified HAMT construction uses the insert Node unique updated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L275-L317
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L275-L317

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

theorem VerifiedHAMT.insertNode_unique_updated [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α β) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (hu : Unique node) (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    Unique res ∧ Updated node res key value := by sorry
