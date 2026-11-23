-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_toRaw_ofRaw
-- name    : VerifiedHAMT.Set.toRaw_ofRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:39.352881+00:00
-- url     : https://prove2.me/theorems/a2b0e5ab-b62a-4e69-889b-0d2ca6b1184a
-- title:
--   Set: to Raw of Raw
-- statement:
--   The Set construction uses the to Raw of Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L75-L77
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L75-L77

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_ofRaw

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.toRaw_ofRaw (raw : Lean.PersistentHashSet α)
    (valid : Valid raw.set) (unique : Unique raw.set.root) :
    (ofRaw raw valid unique).toRaw = raw := by sorry
