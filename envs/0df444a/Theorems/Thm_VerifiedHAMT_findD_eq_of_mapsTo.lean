-- Prove2me | Theorems.Thm_VerifiedHAMT_findD_eq_of_mapsTo
-- name    : VerifiedHAMT.findD_eq_of_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:25.651393+00:00
-- url     : https://prove2.me/theorems/4c8b2942-19b0-40c5-9312-80f4f4f52bc9
-- title:
--   Verified HAMT: find D eq of maps To
-- statement:
--   The Verified HAMT construction uses the find D eq of maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L270-L274
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L270-L274

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

theorem VerifiedHAMT.findD_eq_of_mapsTo [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) (hb : MapsTo key value map) :
    findD map key fallback = value := by sorry
