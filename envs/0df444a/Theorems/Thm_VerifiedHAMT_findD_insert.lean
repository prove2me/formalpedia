-- Prove2me | Theorems.Thm_VerifiedHAMT_findD_insert
-- name    : VerifiedHAMT.findD_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:34:37.558634+00:00
-- url     : https://prove2.me/theorems/90aa3a6c-79ff-408f-8bfc-6d0884e68776
-- title:
--   Verified HAMT: find D insert
-- statement:
--   The Verified HAMT construction uses the find D insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L287-L293
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L287-L293

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findD_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value fallback : β) :
    findD (VerifiedHAMT.insert map key value) q fallback =
      if q == key then value else findD map q fallback := by sorry
