-- Prove2me | Theorems.Thm_VerifiedHAMT_mem_insert_iff
-- name    : VerifiedHAMT.mem_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:09.268381+00:00
-- url     : https://prove2.me/theorems/2ff934ab-271b-4c9b-bab8-fa914091f91a
-- title:
--   Verified HAMT: mem insert iff
-- statement:
--   Exact membership update; uniqueness is not needed.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L330-L335
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L330-L335

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

theorem VerifiedHAMT.mem_insert_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    Mem q (insert map key value) ↔ q = key ∨ Mem q map := by sorry
