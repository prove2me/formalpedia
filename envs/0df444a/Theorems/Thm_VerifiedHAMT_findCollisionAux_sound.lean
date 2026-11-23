-- Prove2me | Theorems.Thm_VerifiedHAMT_findCollisionAux_sound
-- name    : VerifiedHAMT.findCollisionAux_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:35.348686+00:00
-- url     : https://prove2.me/theorems/65d38a70-e4a5-4faf-8127-13a46f8005e6
-- title:
--   Verified HAMT: find Collision Aux sound
-- statement:
--   The Verified HAMT construction uses the find Collision Aux sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L79-L95
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L79-L95

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findCollisionAux_sound [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key : α) (value : β)
    (found : findCollisionAux keys vals hsz i key = some value) :
    ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = key ∧
      vals[j]'(hsz ▸ hj) = value := by sorry
