-- Prove2me | Theorems.Thm_VerifiedHAMT_findCollisionAux_eq_none_iff
-- name    : VerifiedHAMT.findCollisionAux_eq_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:38:02.267295+00:00
-- url     : https://prove2.me/theorems/65f85c9c-b518-467a-8fc4-ba49a879c38f
-- title:
--   Verified HAMT: find Collision Aux eq none iff
-- statement:
--   The Verified HAMT construction uses the find Collision Aux eq none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L136-L158
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L136-L158

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

theorem VerifiedHAMT.findCollisionAux_eq_none_iff [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key : α) :
    findCollisionAux keys vals hsz i key = none ↔
      ∀ (j : Nat) (hj : j < keys.size), i ≤ j → keys[j] ≠ key := by sorry
