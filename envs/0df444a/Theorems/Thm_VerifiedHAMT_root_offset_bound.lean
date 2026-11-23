-- Prove2me | Theorems.Thm_VerifiedHAMT_root_offset_bound
-- name    : VerifiedHAMT.root_offset_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:51.324391+00:00
-- url     : https://prove2.me/theorems/0c00807a-9828-411e-a338-fcdd4c1b7252
-- title:
--   Verified HAMT: root offset bound
-- statement:
--   The Verified HAMT construction uses the root offset bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L34-L36
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Util.lean#L34-L36

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_Util
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap (shift maxDepth)

theorem VerifiedHAMT.root_offset_bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by sorry
