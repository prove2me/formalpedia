-- Prove2me | Theorems.Thm_VerifiedHAMT_unique_insert
-- name    : VerifiedHAMT.unique_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:34.289191+00:00
-- url     : https://prove2.me/theorems/36519525-603b-4028-87b8-39368cc80e5b
-- title:
--   Verified HAMT: unique insert
-- statement:
--   The Verified HAMT construction uses the unique insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L337-L342
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L337-L342

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

theorem VerifiedHAMT.unique_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : Unique (insert map key value).root := by sorry
