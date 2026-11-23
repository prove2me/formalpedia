-- Prove2me | Theorems.Thm_VerifiedHAMT_containsNode_sound
-- name    : VerifiedHAMT.containsNode_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:52.64006+00:00
-- url     : https://prove2.me/theorems/0a0eccbf-f84e-4f2a-9c92-3e100db83079
-- title:
--   Verified HAMT: contains Node sound
-- statement:
--   A successful query cannot invent a key, even in a malformed node.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L66-L93
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L66-L93

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

theorem VerifiedHAMT.containsNode_sound [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (found : containsNode node hash key = true) :
    HasKey key node := by sorry
