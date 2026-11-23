-- Prove2me | Theorems.Thm_VerifiedHAMT_containsNode_complete
-- name    : VerifiedHAMT.containsNode_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:52.692233+00:00
-- url     : https://prove2.me/theorems/524c6344-e019-44ca-bb2c-119cd640de49
-- title:
--   Verified HAMT: contains Node complete
-- statement:
--   On a well-formed node, hash-directed traversal finds every stored key.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L96-L107
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L96-L107

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.containsNode_complete [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : containsNode node (hashAt key) key = true := by sorry
