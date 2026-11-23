-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_insert_self
-- name    : VerifiedHAMT.Set.contains_insert_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:20.878508+00:00
-- url     : https://prove2.me/theorems/3a66ce02-7d47-4776-b272-89ddc0b579ee
-- title:
--   Set: contains insert self
-- statement:
--   The Set construction uses the contains insert self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L125-L126
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L125-L126

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.contains_insert_self [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).contains key = true := by sorry
