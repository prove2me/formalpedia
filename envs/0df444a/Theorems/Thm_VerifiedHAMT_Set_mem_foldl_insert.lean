-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_mem_foldl_insert
-- name    : VerifiedHAMT.Set.mem_foldl_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:59:42.747797+00:00
-- url     : https://prove2.me/theorems/ce1069ee-3183-4b96-85ce-163903c05f43
-- title:
--   Set: mem foldl insert
-- statement:
--   Membership in a bulk insertion is membership in the old set or input list.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L140-L146
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L140-L146

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

theorem VerifiedHAMT.Set.mem_foldl_insert [LawfulBEq α] (keys : List α) (set : Set α) (q : α) :
    q ∈ keys.foldl insert set ↔ q ∈ set ∨ q ∈ keys := by sorry
