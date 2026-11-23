-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_toMap_ofMap
-- name    : VerifiedHAMT.Set.toMap_ofMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:54:35.331091+00:00
-- url     : https://prove2.me/theorems/6c2f6012-6daf-464e-ba9a-99af08d96652
-- title:
--   Set: to Map of Map
-- statement:
--   The Set construction uses the to Map of Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L71-L71
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L71-L71

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

theorem VerifiedHAMT.Set.toMap_ofMap (map : Map α Unit) : (ofMap map).toMap = map := by sorry
