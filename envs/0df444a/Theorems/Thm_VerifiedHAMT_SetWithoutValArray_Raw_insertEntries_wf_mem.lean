-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_wf_mem
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:43:25.484938+00:00
-- url     : https://prove2.me/theorems/ced44a4c-5aff-494b-a231-802e4cfb6eba
-- title:
--   Raw: insert Entries wf mem
-- statement:
--   The Raw construction uses the insert Entries wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L29-L62
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertProofs.lean#L29-L62

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

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_wf_mem [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by sorry
