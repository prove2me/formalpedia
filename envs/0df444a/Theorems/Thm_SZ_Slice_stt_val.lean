-- Prove2me | Theorems.Thm_SZ_Slice_stt_val
-- name    : SZ.Slice.stt_val
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:00:56.590391+00:00
-- url     : https://prove2.me/theorems/bc59f75b-2708-568c-a0e9-7f0300a60af0
-- title:
--   Slice: stt val
-- statement:
--   The state pair realises the state value.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L129-L139
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L129-L139

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.stt_val (he : S.e = (S.m : ℤ) - 1) (j k₀ : ℤ) (k : ℕ) :
    S.W (S.w0 j k₀) k = ((stt S j k₀ k).1 : ℝ) + ((stt S j k₀ k).2 : ℝ) * S.sq := by sorry
