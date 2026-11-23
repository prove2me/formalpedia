-- Prove2me | Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
-- name    : P2M_ZMod_fst_chineseRemainder__e38dff19d888
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:00.70432+00:00
-- url     : https://prove2.me/theorems/46b427f0-be9a-4fd5-8def-a10cdfb1c159
-- title:
--   P2 M ZMod fst chinese Remainder  e38dff19d888: P2 M ZMod fst chinese Remainder  e38dff19d888
-- statement:
--   The P2 M ZMod fst chinese Remainder  e38dff19d888 construction uses the P2 M ZMod fst chinese Remainder  e38dff19d888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L17-L19
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L17-L19

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_fst_chineseRemainder__e38dff19d888 {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).1 = unitsMap (dvd_mul_right m n) x := by sorry

alias «ZMod».«fst_chineseRemainderₓ» := P2M_ZMod_fst_chineseRemainder__e38dff19d888
