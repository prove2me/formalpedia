-- Prove2me | Theorems.Thm_VerifiedHAMT_insertEntries_wf_mem
-- name    : VerifiedHAMT.insertEntries_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:45.786341+00:00
-- url     : https://prove2.me/theorems/dc73928c-68f7-4692-a075-29a67068cabb
-- title:
--   Verified HAMT: insert Entries wf mem
-- statement:
--   The Verified HAMT construction uses the insert Entries wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L61-L94
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L61-L94

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

theorem VerifiedHAMT.insertEntries_wf_mem [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key value)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key value
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by sorry
