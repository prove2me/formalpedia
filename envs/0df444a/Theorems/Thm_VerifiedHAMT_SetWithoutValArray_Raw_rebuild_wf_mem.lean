-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_rebuild_wf_mem
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.rebuild_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:44:13.377949+00:00
-- url     : https://prove2.me/theorems/d9e8853a-699f-4da7-9d93-e10123df6344
-- title:
--   Raw: rebuild wf mem
-- statement:
--   The Raw construction uses the rebuild wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L77-L105
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L77-L105

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.rebuild_wf_mem [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α)
    (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by sorry
