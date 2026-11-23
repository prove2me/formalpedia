-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_ofRaw_toRaw
-- name    : VerifiedHAMT.Set.ofRaw_toRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:33.926574+00:00
-- url     : https://prove2.me/theorems/a3978cdb-b848-46cb-8db5-d516175ad4f9
-- title:
--   Set: of Raw to Raw
-- statement:
--   The Set construction uses the of Raw to Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L79-L81
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L79-L81

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_ofRaw_toRaw

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.ofRaw_toRaw (set : Set α) :
    ofRaw set.toRaw set.toMap.valid set.toMap.unique = set := by sorry
