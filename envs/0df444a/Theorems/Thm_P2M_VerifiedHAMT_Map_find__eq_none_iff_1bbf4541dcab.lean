-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__eq_none_iff_1bbf4541dcab
-- name    : P2M_VerifiedHAMT_Map_find__eq_none_iff_1bbf4541dcab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:12.303024+00:00
-- url     : https://prove2.me/theorems/eabb6a80-12ae-4127-ac5b-0faa2ad93f5a
-- title:
--   P2 M Verified HAMT Map find  eq none iff 1bbf4541dcab: P2 M Verified HAMT Map find  eq none iff 1bbf4541dcab
-- statement:
--   The P2 M Verified HAMT Map find  eq none iff 1bbf4541dcab construction uses the P2 M Verified HAMT Map find  eq none iff 1bbf4541dcab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L134-L136
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L134-L136

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__eq_none_iff_1bbf4541dcab [LawfulBEq α] (map : Map α β) (key : α) :
    map.find? key = none ↔ key ∉ map := by sorry

alias «VerifiedHAMT».«Map».«find?_eq_none_iff» := P2M_VerifiedHAMT_Map_find__eq_none_iff_1bbf4541dcab
