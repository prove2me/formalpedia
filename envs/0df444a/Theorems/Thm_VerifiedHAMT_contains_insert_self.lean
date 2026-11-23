-- Prove2me | Theorems.Thm_VerifiedHAMT_contains_insert_self
-- name    : VerifiedHAMT.contains_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:39.472002+00:00
-- url     : https://prove2.me/theorems/e52e3a1d-1a4f-4874-9be6-9e647352d8dc
-- title:
--   Verified HAMT: contains insert self
-- statement:
--   The Verified HAMT construction uses the contains insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L374-L377
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L374-L377

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

theorem VerifiedHAMT.contains_insert_self [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    contains (insert map key value) key = true := by sorry
