-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_unique
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:37.482021+00:00
-- url     : https://prove2.me/theorems/b781c608-2fa2-4f78-8514-9eb93dc81799
-- title:
--   Raw: insert Entries unique
-- statement:
--   The Raw construction uses the insert Entries unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L33-L47
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Unique.lean#L33-L47

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_unique [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α) (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es), Unique child →
      Unique (childInsert child hmem (nextHash (hashAt key)) key)) :
    Unique (.entries (insertEntries es childInsert (hashAt key) key)) := by sorry
