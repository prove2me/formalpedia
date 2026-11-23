-- Prove2me | Theorems.Thm_VerifiedHAMT_findD_insert_self
-- name    : VerifiedHAMT.findD_insert_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:36:36.675087+00:00
-- url     : https://prove2.me/theorems/041ade90-97a6-44ab-bbf9-876e03ade77e
-- title:
--   Verified HAMT: find D insert self
-- statement:
--   The Verified HAMT construction uses the find D insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L295-L299
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L295-L299

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

theorem VerifiedHAMT.findD_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) : findD (VerifiedHAMT.insert map key value) key fallback = value := by sorry
