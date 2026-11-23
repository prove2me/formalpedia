-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedEntries_eq
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.insertSizedEntries_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:43:48.109971+00:00
-- url     : https://prove2.me/theorems/23118408-e116-4841-b77a-4674d6fc1a0c
-- title:
--   Raw: insert Sized Entries eq
-- statement:
--   The Raw construction uses the insert Sized Entries eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L138-L152
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/InsertSized.lean#L138-L152

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.insertSizedEntries_eq [BEq α] [Hashable α]
    (es : Array (Entry α (Node α))) (size : Nat)
    (childInsert : (child : Node α) → .ref child ∈ es →
      Nat → USize → α → SizedRaw α)
    (childModel : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key =
        ⟨⟨childModel child hmem (nextHash h) key⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key =
      ⟨⟨.entries (insertEntries es childModel h key)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by sorry
