-- Prove2me | Theorems.Thm_VerifiedHAMT_containsNode_entries
-- name    : VerifiedHAMT.containsNode_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:49.12581+00:00
-- url     : https://prove2.me/theorems/59f8c80e-f4fa-439d-825b-fd7ca71b296b
-- title:
--   Verified HAMT: contains Node entries
-- statement:
--   A lookup equation without the termination proof's dependent match.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L47-L59
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L47-L59

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

theorem VerifiedHAMT.containsNode_entries [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    containsNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => false
        | .entry key' _ => key == key'
        | .ref child => containsNode child (nextHash hash) key
      else false := by sorry
