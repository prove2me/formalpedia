-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_insert
-- name    : VerifiedHAMT.Set.contains_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:16.85605+00:00
-- url     : https://prove2.me/theorems/18871742-67ba-44fe-a668-573d673f2476
-- title:
--   Set: contains insert
-- statement:
--   The Set construction uses the contains insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L121-L123
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L121-L123

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert
public import Theorems.Thm_VerifiedHAMT_contains_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.contains_insert [LawfulBEq α] (set : Set α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) := by sorry
