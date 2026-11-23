-- Prove2me | Theorems.Thm_VerifiedHAMT_keyCount_insert
-- name    : VerifiedHAMT.keyCount_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:24.824925+00:00
-- url     : https://prove2.me/theorems/1a9bf2db-7ec1-4c6c-90fb-0dbd7dbdc430
-- title:
--   Verified HAMT: key Count insert
-- statement:
--   Insertion adds one key exactly when the key is new.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L386-L417
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L386-L417

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

theorem VerifiedHAMT.keyCount_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) :
    keyCount (insert map key value).root =
      if contains map key then keyCount map.root else keyCount map.root + 1 := by sorry
