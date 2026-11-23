-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_size_empty
-- name    : VerifiedHAMT.Set.size_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:11.135819+00:00
-- url     : https://prove2.me/theorems/586c934d-5386-484a-885c-e8f2732aee78
-- title:
--   Set: size empty
-- statement:
--   The Set construction uses the size empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L112-L112
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L112-L112

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_size_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.size_empty : (∅ : Set α).size = 0 := by sorry
