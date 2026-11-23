-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_MapsTo_functional
-- name    : VerifiedHAMT.Map.MapsTo.functional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:01:42.82179+00:00
-- url     : https://prove2.me/theorems/1d1bd01f-6617-47be-899c-4a433d63341f
-- title:
--   Maps To: functional
-- statement:
--   The Maps To construction uses the functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L169-L171
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L169-L171

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_HasBinding_functional

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.MapsTo.functional {map : Map α β} {key : α} {v w : β}
    (hv : map.MapsTo key v) (hw : map.MapsTo key w) : v = w := by sorry
