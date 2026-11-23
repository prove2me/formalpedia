-- Prove2me | Theorems.Thm_VerifiedHAMT_mapsTo_insert_iff
-- name    : VerifiedHAMT.mapsTo_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:44.528104+00:00
-- url     : https://prove2.me/theorems/accfd7ef-6a99-49d6-ba1d-9a345d0b26cf
-- title:
--   Verified HAMT: maps To insert iff
-- statement:
--   The complete key/value update law. Replacing a key discards its old binding;
--   all other bindings are preserved. `Unique` rules out duplicate collision keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L346-L353
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L346-L353

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

theorem VerifiedHAMT.mapsTo_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) :
    MapsTo q w (insert map key value) ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ MapsTo q w map) := by sorry
