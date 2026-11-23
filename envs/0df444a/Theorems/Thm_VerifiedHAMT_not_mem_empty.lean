-- Prove2me | Theorems.Thm_VerifiedHAMT_not_mem_empty
-- name    : VerifiedHAMT.not_mem_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:14.457042+00:00
-- url     : https://prove2.me/theorems/1761c1f4-6c27-4af0-8a70-6e935409df0b
-- title:
--   Verified HAMT: not mem empty
-- statement:
--   The Verified HAMT construction uses the not mem empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L146-L148
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L146-L148

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.not_mem_empty [BEq α] [Hashable α] (key : α) :
    ¬ Mem key (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) := by sorry
