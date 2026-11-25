-- Prove2me | Theorems.Thm_SZ_Slice_stt_zero
-- name    : SZ.Slice.stt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:25.048915+00:00
-- url     : https://prove2.me/theorems/03d6818e-00de-4df5-b486-3f957156a1ea
-- title:
--   Slice: stt zero
-- statement:
--   The Slice construction uses the stt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L121-L122
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L121-L122

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.stt_zero (S : Slice) (j k₀ : ℤ) :
    stt S j k₀ 0 = (-S.p * j * (S.m : ℤ), (S.p * k₀ + 1) * (S.m : ℤ)) := by sorry
