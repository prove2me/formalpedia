-- Prove2me | Theorems.Thm_P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2
-- name    : P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:21.931968+00:00
-- url     : https://prove2.me/theorems/11ebafc3-67a1-467a-8b7e-353ff5717964
-- title:
--   P2 M Verified HAMT find  is Some eq contains a614a0a0acb2: P2 M Verified HAMT find  is Some eq contains a614a0a0acb2
-- statement:
--   The P2 M Verified HAMT find  is Some eq contains a614a0a0acb2 construction uses the P2 M Verified HAMT find  is Some eq contains a614a0a0acb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L230-L239
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L230-L239

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

theorem P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2 [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    (VerifiedHAMT.find? map key).isSome = VerifiedHAMT.contains map key := by sorry

alias «VerifiedHAMT».«find?_isSome_eq_contains» := P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2
