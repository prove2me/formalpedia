-- Prove2me | Theorems.Thm_VerifiedHAMT_insertCollision_size_eq
-- name    : VerifiedHAMT.insertCollision_size_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:17.883804+00:00
-- url     : https://prove2.me/theorems/d797c911-b58a-4eb2-92cd-f56b4394d7ec
-- title:
--   Verified HAMT: insert Collision size eq
-- statement:
--   The Verified HAMT construction uses the insert Collision size eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L135-L140
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L135-L140

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertCollision_size_eq [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (key : α) (value : β) :
    (getCollisionNodeSize (insertCollision keys vals hsz key value) == keys.size) = keys.contains key := by sorry
