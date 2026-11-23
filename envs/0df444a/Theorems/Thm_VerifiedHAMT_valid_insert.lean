-- Prove2me | Theorems.Thm_VerifiedHAMT_valid_insert
-- name    : VerifiedHAMT.valid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:46.675811+00:00
-- url     : https://prove2.me/theorems/c13497c8-0d15-4d97-843a-42dd3b01bd43
-- title:
--   Verified HAMT: valid insert
-- statement:
--   Insertion preserves the routing invariant even when the input has duplicate keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L322-L327
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L322-L327

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

theorem VerifiedHAMT.valid_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    Valid (insert map key value) := by sorry
