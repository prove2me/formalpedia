-- Prove2me | Theorems.Thm_VerifiedHAMT_contains_eq_false_iff
-- name    : VerifiedHAMT.contains_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:46.742242+00:00
-- url     : https://prove2.me/theorems/b7c2b6ba-b151-4e5a-9bcd-ed41d12bd7c3
-- title:
--   Verified HAMT: contains eq false iff
-- statement:
--   The Verified HAMT construction uses the contains eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L120-L124
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L120-L124

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

theorem VerifiedHAMT.contains_eq_false_iff [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = false ↔ ¬ Mem key map := by sorry
