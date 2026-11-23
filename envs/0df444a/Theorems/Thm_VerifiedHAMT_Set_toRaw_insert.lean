-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_toRaw_insert
-- name    : VerifiedHAMT.Set.toRaw_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:55:52.626867+00:00
-- url     : https://prove2.me/theorems/563e4741-35cc-486a-9cc9-639d933b4dfa
-- title:
--   Set: to Raw insert
-- statement:
--   The Set construction uses the to Raw insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L91-L92
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L91-L92

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.toRaw_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).toRaw = ⟨VerifiedHAMT.insert set.toMap.toRaw key ()⟩ := by sorry
