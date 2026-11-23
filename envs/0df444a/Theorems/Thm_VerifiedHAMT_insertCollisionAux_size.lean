-- Prove2me | Theorems.Thm_VerifiedHAMT_insertCollisionAux_size
-- name    : VerifiedHAMT.insertCollisionAux_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:51.472823+00:00
-- url     : https://prove2.me/theorems/11e76c97-19fa-46ef-b38c-6b843e811dba
-- title:
--   Verified HAMT: insert Collision Aux size
-- statement:
--   The Verified HAMT construction uses the insert Collision Aux size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L106-L133
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L106-L133

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

theorem VerifiedHAMT.insertCollisionAux_size [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (i : Nat) (key : α) (value : β) :
    getCollisionNodeSize (insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value) =
      if (keys.drop i).contains key then keys.size else keys.size + 1 := by sorry
