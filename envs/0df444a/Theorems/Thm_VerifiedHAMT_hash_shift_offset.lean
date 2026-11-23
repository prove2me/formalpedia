-- Prove2me | Theorems.Thm_VerifiedHAMT_hash_shift_offset
-- name    : VerifiedHAMT.hash_shift_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:54.122304+00:00
-- url     : https://prove2.me/theorems/cf38cd8e-6325-46b1-9652-3d5870d62e6c
-- title:
--   Verified HAMT: hash shift offset
-- statement:
--   The Verified HAMT construction uses the hash shift offset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L13-L25
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L13-L25

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_Util
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap (shift maxDepth)

theorem VerifiedHAMT.hash_shift_offset (h offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    h >>> (offset + shift) = nextHash (h >>> offset) := by sorry
