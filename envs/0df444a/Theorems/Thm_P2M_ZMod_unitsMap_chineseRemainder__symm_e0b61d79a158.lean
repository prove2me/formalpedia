-- Prove2me | Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
-- name    : P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:11.993602+00:00
-- url     : https://prove2.me/theorems/8453fba4-2d33-4cf7-b0ce-f3b4095f3069
-- title:
--   P2 M ZMod units Map chinese Remainder  symm e0b61d79a158: P2 M ZMod units Map chinese Remainder  symm e0b61d79a158
-- statement:
--   The P2 M ZMod units Map chinese Remainder  symm e0b61d79a158 construction uses the P2 M ZMod units Map chinese Remainder  symm e0b61d79a158 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L26-L29
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L26-L29

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158 {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_right m n)) ((chineseRemainderₓ h).symm (x, y)) = x := by sorry

alias «ZMod».«unitsMap_chineseRemainderₓ_symm» := P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
