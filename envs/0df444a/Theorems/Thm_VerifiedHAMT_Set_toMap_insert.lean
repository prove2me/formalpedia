-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_toMap_insert
-- name    : VerifiedHAMT.Set.toMap_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:50.355937+00:00
-- url     : https://prove2.me/theorems/4e934297-5eb2-4926-b4bc-8b767ec3bcf6
-- title:
--   Set: to Map insert
-- statement:
--   The Set construction uses the to Map insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L88-L89
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L88-L89

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.toMap_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).toMap = set.toMap.insert key () := by sorry
