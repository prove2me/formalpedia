-- Prove2me | Theorems.Thm_VerifiedHAMT_DistinctKeys_nodup_toList
-- name    : VerifiedHAMT.DistinctKeys.nodup_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:34.126145+00:00
-- url     : https://prove2.me/theorems/73d87133-34aa-413b-a6f7-dec55e90860e
-- title:
--   Distinct Keys: nodup to List
-- statement:
--   The Distinct Keys construction uses the nodup to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L87-L93
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L87-L93

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.DistinctKeys.nodup_toList {keys : Array α} (h : DistinctKeys keys) :
    keys.toList.Nodup := by sorry
