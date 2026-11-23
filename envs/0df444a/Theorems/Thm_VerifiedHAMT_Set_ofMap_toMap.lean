-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_ofMap_toMap
-- name    : VerifiedHAMT.Set.ofMap_toMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:54:36.140712+00:00
-- url     : https://prove2.me/theorems/0c842553-d92f-46a8-96b6-6cabcfb0ae09
-- title:
--   Set: of Map to Map
-- statement:
--   The Set construction uses the of Map to Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L73-L73
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L73-L73

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

theorem VerifiedHAMT.Set.ofMap_toMap (set : Set α) : ofMap set.toMap = set := by sorry
