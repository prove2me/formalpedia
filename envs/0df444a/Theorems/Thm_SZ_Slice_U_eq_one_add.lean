-- Prove2me | Theorems.Thm_SZ_Slice_U_eq_one_add
-- name    : SZ.Slice.U_eq_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:21.070801+00:00
-- url     : https://prove2.me/theorems/93777bc9-0d24-4d52-b0e4-3d4762bf0215
-- title:
--   Slice: U eq one add
-- statement:
--   The Slice construction uses the U eq one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L90-L91
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L90-L91

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.U_eq_one_add (he : S.e = (S.m : ℤ) - 1) : S.U = 1 + S.sq := by sorry
