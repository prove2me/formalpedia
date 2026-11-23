-- Prove2me | Theorems.Thm_VerifiedHAMT_insertCollisionAux_mem
-- name    : VerifiedHAMT.insertCollisionAux_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:48.938465+00:00
-- url     : https://prove2.me/theorems/2f73a85c-48c3-4e5f-a07a-4b9ce08407c9
-- title:
--   Verified HAMT: insert Collision Aux mem
-- statement:
--   The Verified HAMT construction uses the insert Collision Aux mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L19-L32
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L19-L32

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

theorem VerifiedHAMT.insertCollisionAux_mem [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key q : α) (value : β) :
    HasKey q (insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value).val ↔
      q = key ∨ HasKey q (.collision keys vals hsz) := by sorry
