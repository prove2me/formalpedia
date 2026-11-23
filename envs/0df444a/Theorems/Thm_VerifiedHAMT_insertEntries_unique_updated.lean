-- Prove2me | Theorems.Thm_VerifiedHAMT_insertEntries_unique_updated
-- name    : VerifiedHAMT.insertEntries_unique_updated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:23.996018+00:00
-- url     : https://prove2.me/theorems/934a5dd6-0616-4f20-bddb-ee1b8617f9cb
-- title:
--   Verified HAMT: insert Entries unique updated
-- statement:
--   The Verified HAMT construction uses the insert Entries unique updated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L96-L122
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L96-L122

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

theorem VerifiedHAMT.insertEntries_unique_updated [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := childInsert child hmem (nextHash (hashAt key)) key value
      Unique child → Unique res ∧ Updated child res key value) :
    letI res := insertEntries es childInsert (hashAt key) key value
    Unique (.entries res) ∧ Updated (.entries es) (.entries res) key value := by sorry
