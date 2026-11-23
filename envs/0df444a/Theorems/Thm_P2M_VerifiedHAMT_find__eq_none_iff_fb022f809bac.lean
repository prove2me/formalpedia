-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
-- name    : P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:54.979973+00:00
-- url     : https://prove2.me/theorems/d48573b8-52bd-4557-b7a5-5f8e620e561e
-- title:
--   P2 M Verified HAMT find  eq none iff fb022f809bac: P2 M Verified HAMT find  eq none iff fb022f809bac
-- statement:
--   The P2 M Verified HAMT find  eq none iff fb022f809bac construction uses the P2 M Verified HAMT find  eq none iff fb022f809bac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L222-L224
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L222-L224

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

theorem P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    VerifiedHAMT.find? map key = none ↔ ¬ Mem key map := by sorry

alias «VerifiedHAMT».«find?_eq_none_iff» := P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
