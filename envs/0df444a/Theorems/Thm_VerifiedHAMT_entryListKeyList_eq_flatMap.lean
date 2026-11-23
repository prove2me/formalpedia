-- Prove2me | Theorems.Thm_VerifiedHAMT_entryListKeyList_eq_flatMap
-- name    : VerifiedHAMT.entryListKeyList_eq_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:03.935806+00:00
-- url     : https://prove2.me/theorems/bac2a0ef-dd0d-4386-935b-1f350a709e20
-- title:
--   Verified HAMT: entry List Key List eq flat Map
-- statement:
--   The Verified HAMT construction uses the entry List Key List eq flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L48-L52
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L48-L52

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.entryListKeyList_eq_flatMap (es : List (Entry α β (Node α β))) :
    entryListKeyList es = es.flatMap entryKeyList := by sorry
