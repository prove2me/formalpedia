-- Prove2me | Theorems.Thm_P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff
-- name    : P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:11.277735+00:00
-- url     : https://prove2.me/theorems/4abeaa0d-e5a5-430d-89af-0198cc8f3d92
-- title:
--   P2 M ZMod fst comp chinese Remainder  e39583bda7ff: P2 M ZMod fst comp chinese Remainder  e39583bda7ff
-- statement:
--   The P2 M ZMod fst comp chinese Remainder  e39583bda7ff construction uses the P2 M ZMod fst comp chinese Remainder  e39583bda7ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L21-L23
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L21-L23

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.fst (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      unitsMap (dvd_mul_right m n) := by sorry

alias «ZMod».«fst_comp_chineseRemainderₓ» := P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff
