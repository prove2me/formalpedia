-- Prove2me | Theorems.Thm_VerifiedHAMT_contains_eq_true_iff
-- name    : VerifiedHAMT.contains_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:32.870205+00:00
-- url     : https://prove2.me/theorems/bec67b23-f2f5-4e34-9d9c-3d8a351a14ad
-- title:
--   Verified HAMT: contains eq true iff
-- statement:
--   `contains` is exactly structural key membership, assuming the map invariant.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L115-L118
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L115-L118

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.contains_eq_true_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map := by sorry
