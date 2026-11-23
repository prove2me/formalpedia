-- Prove2me | Theorems.Thm_VerifiedHAMT_findNode_sound
-- name    : VerifiedHAMT.findNode_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:40.133361+00:00
-- url     : https://prove2.me/theorems/fd6c8897-80e1-4781-b37b-e9bccc21c707
-- title:
--   Verified HAMT: find Node sound
-- statement:
--   Successful lookup returns a stored binding even without routing or uniqueness.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L98-L130
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L98-L130

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findNode_sound [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (value : β) (found : findNode node hash key = some value) :
    HasBinding key value node := by sorry
