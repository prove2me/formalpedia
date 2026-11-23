-- Prove2me | Theorems.Thm_VerifiedHAMT_insertEntries_eq
-- name    : VerifiedHAMT.insertEntries_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:22.09316+00:00
-- url     : https://prove2.me/theorems/ade42e6c-0dda-43ec-be53-cac7e01d8aee
-- title:
--   Verified HAMT: insert Entries eq
-- statement:
--   Logically, `insertEntries` writes one entry into the selected slot; the
--   clearing write only matters at runtime.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Insert.lean#L70-L80
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Insert.lean#L70-L80

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_Bindings
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Insert
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertEntries_eq [BEq α] (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β) (hi : slot h < es.size) :
    insertEntries es childInsert h key value =
      es.set (slot h) (match es[slot h], Array.getElem_mem hi with
        | .null, _ => .entry key value
        | .entry k v, _ => if key == k then .entry key value
            else .ref (mkCollisionNode k v key value)
        | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key value)) hi := by sorry
