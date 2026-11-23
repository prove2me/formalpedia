-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_findD_empty
-- name    : VerifiedHAMT.Map.findD_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:28.539748+00:00
-- url     : https://prove2.me/theorems/53c9a132-3e14-459b-a9ef-4fb802bc0297
-- title:
--   Map: find D empty
-- statement:
--   The Map construction uses the find D empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L186-L187
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L186-L187

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.findD_empty [LawfulBEq α] (key : α) (fallback : β) :
    (∅ : Map α β).findD key fallback = fallback := by sorry
