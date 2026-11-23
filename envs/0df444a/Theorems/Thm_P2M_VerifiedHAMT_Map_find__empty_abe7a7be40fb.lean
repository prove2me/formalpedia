-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_Map_find__empty_abe7a7be40fb
-- name    : P2M_VerifiedHAMT_Map_find__empty_abe7a7be40fb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:01:57.275898+00:00
-- url     : https://prove2.me/theorems/b8d5b5cc-dd14-480e-8ff2-0d610333ea19
-- title:
--   P2 M Verified HAMT Map find  empty abe7a7be40fb: P2 M Verified HAMT Map find  empty abe7a7be40fb
-- statement:
--   The P2 M Verified HAMT Map find  empty abe7a7be40fb construction uses the P2 M Verified HAMT Map find  empty abe7a7be40fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L183-L184
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L183-L184

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem P2M_VerifiedHAMT_Map_find__empty_abe7a7be40fb [LawfulBEq α] (key : α) :
    (∅ : Map α β).find? key = none := by sorry

alias «VerifiedHAMT».«Map».«find?_empty» := P2M_VerifiedHAMT_Map_find__empty_abe7a7be40fb
