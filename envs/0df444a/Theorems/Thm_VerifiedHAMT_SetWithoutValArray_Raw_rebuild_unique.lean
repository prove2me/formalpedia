-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_rebuild_unique
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.rebuild_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:44:36.258082+00:00
-- url     : https://prove2.me/theorems/ec44b6c1-9be1-46b3-9db6-463168621577
-- title:
--   Raw: rebuild unique
-- statement:
--   The Raw construction uses the rebuild unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L62-L88
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L62-L88

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.rebuild_unique [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUnique :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k, Unique (childInsert n (hashAt k) k))
    (keys : Array α) (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es))
    (hu : Unique (.entries es)) :
    Unique (.entries (rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es)) := by sorry
