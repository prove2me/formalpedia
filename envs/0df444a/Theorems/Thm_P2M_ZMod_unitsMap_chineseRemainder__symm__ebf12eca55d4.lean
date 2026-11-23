-- Prove2me | Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
-- name    : P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:48.263731+00:00
-- url     : https://prove2.me/theorems/5c89966f-1c27-418b-94dd-727ad5bfc959
-- title:
--   P2 M ZMod units Map chinese Remainder  symm  ebf12eca55d4: P2 M ZMod units Map chinese Remainder  symm  ebf12eca55d4
-- statement:
--   The P2 M ZMod units Map chinese Remainder  symm  ebf12eca55d4 construction uses the P2 M ZMod units Map chinese Remainder  symm  ebf12eca55d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L42-L45
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L42-L45

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4 {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_left n m)) ((chineseRemainderₓ h).symm (x, y)) = y := by sorry

alias «ZMod».«unitsMap_chineseRemainderₓ_symm'» := P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
