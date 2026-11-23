-- Prove2me | Theorems.Thm_VerifiedHAMT_insertSizedRaw_eq
-- name    : VerifiedHAMT.insertSizedRaw_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:00.891771+00:00
-- url     : https://prove2.me/theorems/6fcaae71-5374-4b64-bab0-4044b3baa4e0
-- title:
--   Verified HAMT: insert Sized Raw eq
-- statement:
--   The Verified HAMT construction uses the insert Sized Raw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L179-L196
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L179-L196

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

theorem VerifiedHAMT.insertSizedRaw_eq [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) :
    insertSizedRaw levels offset s h key value =
      ⟨⟨insertNode levels offset s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by sorry
