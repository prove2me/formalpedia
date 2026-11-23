-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_ofRaw_toRaw
-- name    : VerifiedHAMT.Map.ofRaw_toRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:06.79711+00:00
-- url     : https://prove2.me/theorems/8e59ae58-f745-46e3-83bc-449eb83dec09
-- title:
--   Map: of Raw to Raw
-- statement:
--   The Map construction uses the of Raw to Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L103-L111
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L103-L111

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

theorem VerifiedHAMT.Map.ofRaw_toRaw (map : Map α β) :
    ofRaw map.toRaw map.valid map.unique = map := by sorry
