-- Prove2me | Theorems.Thm_VerifiedHAMT_mapsTo_insert_self
-- name    : VerifiedHAMT.mapsTo_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:42.709605+00:00
-- url     : https://prove2.me/theorems/4564c5ae-b298-4fb2-9900-a7f26c3de793
-- title:
--   Verified HAMT: maps To insert self
-- statement:
--   The Verified HAMT construction uses the maps To insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L355-L358
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L355-L358

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

theorem VerifiedHAMT.mapsTo_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value w : β) : MapsTo key w (insert map key value) ↔ w = value := by sorry
