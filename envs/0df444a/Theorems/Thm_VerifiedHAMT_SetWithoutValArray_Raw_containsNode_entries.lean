-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_entries
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.containsNode_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:39:42.671829+00:00
-- url     : https://prove2.me/theorems/966d0a78-b8ac-4b9c-87fa-7b48e37a0c3d
-- title:
--   Raw: contains Node entries
-- statement:
--   A lookup equation without the termination proof's dependent match.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L44-L56
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean#L44-L56

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.containsNode_entries [BEq α] (es : Array (Entry α (Node α)))
    (hash : USize) (key : α) :
    containsNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => false
        | .entry key' => key == key'
        | .ref child => containsNode child (nextHash hash) key
      else false := by sorry
