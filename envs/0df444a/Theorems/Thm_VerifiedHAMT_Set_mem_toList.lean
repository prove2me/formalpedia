-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_mem_toList
-- name    : VerifiedHAMT.Set.mem_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:12.38249+00:00
-- url     : https://prove2.me/theorems/a54cb108-ec93-4361-9d52-c17196b1c0a6
-- title:
--   Set: mem to List
-- statement:
--   The Set construction uses the mem to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L103-L104
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L103-L104

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

theorem VerifiedHAMT.Set.mem_toList (set : Set α) (key : α) : key ∈ set.toList ↔ key ∈ set := by sorry
