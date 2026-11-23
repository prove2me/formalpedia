-- Prove2me | Theorems.Thm_VerifiedHAMT_insertCollisionAux_unique_updated
-- name    : VerifiedHAMT.insertCollisionAux_unique_updated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:35:08.458061+00:00
-- url     : https://prove2.me/theorems/02b26ce2-cef1-48b6-b45f-fe48254acd31
-- title:
--   Verified HAMT: insert Collision Aux unique updated
-- statement:
--   The Verified HAMT construction uses the insert Collision Aux unique updated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L34-L59
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L34-L59

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

theorem VerifiedHAMT.insertCollisionAux_unique_updated [BEq α] [LawfulBEq α] (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (hu : DistinctKeys keys) (i : Nat) (key : α) (value : β)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    letI res := insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value
    Unique res.val ∧ Updated (.collision keys vals hsz) res.val key value := by sorry
