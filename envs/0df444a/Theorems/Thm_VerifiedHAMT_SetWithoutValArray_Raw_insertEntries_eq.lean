-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_eq
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:42:54.714771+00:00
-- url     : https://prove2.me/theorems/283ee245-3314-497a-a4d5-49683527d7cd
-- title:
--   Raw: insert Entries eq
-- statement:
--   Logically, `insertEntries` writes one entry into the selected slot; the
--   clearing write only matters at runtime.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Insert.lean#L66-L76
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Insert.lean#L66-L76

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift branching maxDepth maxCollisions)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_eq [BEq α] (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α) (hi : slot h < es.size) :
    insertEntries es childInsert h key =
      es.set (slot h) (match es[slot h], Array.getElem_mem hi with
        | .null, _ => .entry key
        | .entry k, _ => if key == k then .entry key
            else .ref (mkCollisionNode k key)
        | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key)) hi := by sorry
