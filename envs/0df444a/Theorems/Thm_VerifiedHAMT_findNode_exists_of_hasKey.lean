-- Prove2me | Theorems.Thm_VerifiedHAMT_findNode_exists_of_hasKey
-- name    : VerifiedHAMT.findNode_exists_of_hasKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:13.293628+00:00
-- url     : https://prove2.me/theorems/7fe068cd-0509-4079-ab73-e61fc79976ce
-- title:
--   Verified HAMT: find Node exists of has Key
-- statement:
--   Every stored key has a lookup result under routing alone. Duplicate keys may
--   have several bindings, but the algorithm still returns one of them.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L162-L187
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L162-L187

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findNode_exists_of_hasKey [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : ∃ value, findNode node (hashAt key) key = some value := by sorry
