-- Prove2me | Theorems.Thm_VerifiedHAMT_contains_insert
-- name    : VerifiedHAMT.contains_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:42.81223+00:00
-- url     : https://prove2.me/theorems/ae9455d4-5842-4605-883f-193655e1fcb9
-- title:
--   Verified HAMT: contains insert
-- statement:
--   The previously proved lookup composes with the verified insertion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L367-L372
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L367-L372

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

theorem VerifiedHAMT.contains_insert [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    contains (insert map key value) q = ((q == key) || contains map q) := by sorry
