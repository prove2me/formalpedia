-- Prove2me | Theorems.Thm_VerifiedHAMT_offset_add_shift
-- name    : VerifiedHAMT.offset_add_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:56.130429+00:00
-- url     : https://prove2.me/theorems/e3d5a38a-bd52-461e-934d-83d2b6c51a08
-- title:
--   Verified HAMT: offset add shift
-- statement:
--   The Verified HAMT construction uses the offset add shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L27-L32
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L27-L32

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_Util
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap (shift maxDepth)

theorem VerifiedHAMT.offset_add_shift (offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    (offset + shift).toNat = offset.toNat + 5 := by sorry
