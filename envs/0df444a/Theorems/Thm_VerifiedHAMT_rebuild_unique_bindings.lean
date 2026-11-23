-- Prove2me | Theorems.Thm_VerifiedHAMT_rebuild_unique_bindings
-- name    : VerifiedHAMT.rebuild_unique_bindings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:24.43783+00:00
-- url     : https://prove2.me/theorems/6b2bc2ab-13a1-4825-ac49-df6126b0a282
-- title:
--   Verified HAMT: rebuild unique bindings
-- statement:
--   Rebuilding preserves every binding of a distinct bucket. The accumulator
--   must not already contain a key in the unprocessed suffix.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L226-L273
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L226-L273

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

theorem VerifiedHAMT.rebuild_unique_bindings [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUpd :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        Unique res ∧ Updated n res k v)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (distinct : DistinctKeys keys) (i : Nat)
    (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) (hu : Unique (.entries es))
    (disjoint : ∀ (j : Nat) (hj : j < keys.size), i ≤ j → ¬ HasKey keys[j] (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    Unique (.entries res) ∧
      ∀ q w, HasBinding q w (.entries res) ↔
        HasBinding q w (.entries es) ∨
          ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q ∧ vals[j]'(hsz ▸ hj) = w := by sorry
