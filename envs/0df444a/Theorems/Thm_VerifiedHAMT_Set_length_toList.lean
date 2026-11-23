-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_length_toList
-- name    : VerifiedHAMT.Set.length_toList
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:03:24.674547+00:00
-- url     : https://prove2.me/theorems/4aef006b-84ea-4369-925a-96d8f1c99364
-- title:
--   Set: length to List
-- statement:
--   `size` is the number of elements.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L109-L110
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L109-L110

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

theorem VerifiedHAMT.Set.length_toList (set : Set α) : set.toList.length = set.size := by sorry
