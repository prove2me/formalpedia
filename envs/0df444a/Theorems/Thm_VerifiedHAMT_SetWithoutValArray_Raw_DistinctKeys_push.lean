-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_push
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:02.073319+00:00
-- url     : https://prove2.me/theorems/d0e87565-7fd6-41c2-b1e8-7aa8d28adc36
-- title:
--   Distinct Keys: push
-- statement:
--   The Distinct Keys construction uses the push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L201-L203
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L201-L203

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.push {keys : Array α} (hu : DistinctKeys keys)
    {key : α} (fresh : key ∉ keys) : DistinctKeys (keys.push key) := by sorry
