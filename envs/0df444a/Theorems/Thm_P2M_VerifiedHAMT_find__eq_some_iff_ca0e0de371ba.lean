-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
-- name    : P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:07.663804+00:00
-- url     : https://prove2.me/theorems/c7634f20-2e19-4101-ba87-66b65751d4ba
-- title:
--   P2 M Verified HAMT find  eq some iff ca0e0de371ba: P2 M Verified HAMT find  eq some iff ca0e0de371ba
-- statement:
--   The P2 M Verified HAMT find  eq some iff ca0e0de371ba construction uses the P2 M Verified HAMT find  eq some iff ca0e0de371ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L217-L220
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L217-L220

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

theorem P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : VerifiedHAMT.find? map key = some value ↔ MapsTo key value map := by sorry

alias «VerifiedHAMT».«find?_eq_some_iff» := P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
