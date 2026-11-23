-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_toRaw_empty
-- name    : VerifiedHAMT.Map.toRaw_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:18.164963+00:00
-- url     : https://prove2.me/theorems/bd6bd8b4-d868-404d-adbc-0dec367fbb11
-- title:
--   Map: to Raw empty
-- statement:
--   The Map construction uses the to Raw empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L117-L117
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L117-L117

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.toRaw_empty : (∅ : Map α β).toRaw = Lean.PersistentHashMap.empty := by sorry
