-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_mem_ofList
-- name    : VerifiedHAMT.Set.mem_ofList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:41.459908+00:00
-- url     : https://prove2.me/theorems/89bd2be3-b116-4b16-85e7-0e7a0572c734
-- title:
--   Set: mem of List
-- statement:
--   The Set construction uses the mem of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L148-L150
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L148-L150

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

theorem VerifiedHAMT.Set.mem_ofList [LawfulBEq α] (keys : List α) (key : α) :
    key ∈ ofList keys ↔ key ∈ keys := by sorry
