-- Prove2me | Theorems.Thm_VerifiedHAMT_insertSizedNoExpand_eq
-- name    : VerifiedHAMT.insertSizedNoExpand_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:38:02.225829+00:00
-- url     : https://prove2.me/theorems/5577a5bc-b155-45bc-945f-d0fcb72f51e2
-- title:
--   Verified HAMT: insert Sized No Expand eq
-- statement:
--   The Verified HAMT construction uses the insert Sized No Expand eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L158-L177
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean#L158-L177

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

theorem VerifiedHAMT.insertSizedNoExpand_eq [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) :
    insertSizedNoExpand s h key value =
      ⟨⟨insertNoExpand s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by sorry
