-- Prove2me | Theorems.Thm_VerifiedHAMT_Set_contains_empty
-- name    : VerifiedHAMT.Set.contains_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:56:12.583227+00:00
-- url     : https://prove2.me/theorems/ddc3fec5-2e03-4411-856c-baaac8060420
-- title:
--   Set: contains empty
-- statement:
--   The Set construction uses the contains empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L118-L119
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean#L118-L119

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_empty
public import Theorems.Thm_VerifiedHAMT_contains_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]

theorem VerifiedHAMT.Set.contains_empty [LawfulBEq α] (key : α) :
    (∅ : Set α).contains key = false := by sorry
