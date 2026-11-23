-- Prove2me | Theorems.Thm_VerifiedHAMT_insertSizedEntries_eq
-- name    : VerifiedHAMT.insertSizedEntries_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:47.567875+00:00
-- url     : https://prove2.me/theorems/c0f0aca6-d632-49b1-bb64-952e5ac05853
-- title:
--   Verified HAMT: insert Sized Entries eq
-- statement:
--   The Verified HAMT construction uses the insert Sized Entries eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L142-L156
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L142-L156

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertSizedEntries_eq [BEq α] [Hashable α]
    (es : Array (Entry α β (Node α β))) (size : Nat)
    (childInsert : (child : Node α β) → .ref child ∈ es →
      Nat → USize → α → β → SizedRaw α β)
    (childModel : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key value =
        ⟨⟨childModel child hmem (nextHash h) key value⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key value =
      ⟨⟨.entries (insertEntries es childModel h key value)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by sorry
