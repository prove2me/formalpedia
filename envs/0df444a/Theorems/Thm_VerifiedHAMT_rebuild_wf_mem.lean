-- Prove2me | Theorems.Thm_VerifiedHAMT_rebuild_wf_mem
-- name    : VerifiedHAMT.rebuild_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:21.791716+00:00
-- url     : https://prove2.me/theorems/72561323-37a4-4f6b-92cb-742da4fe1f9c
-- title:
--   Verified HAMT: rebuild wf mem
-- statement:
--   The Verified HAMT construction uses the rebuild wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L152-L180
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L152-L180

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

theorem VerifiedHAMT.rebuild_wf_mem [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by sorry
