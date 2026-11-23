-- Prove2me | Theorems.Thm_P2M_ZMod_snd_comp_chineseRemainder__e253f5662d04
-- name    : P2M_ZMod_snd_comp_chineseRemainder__e253f5662d04
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:12.722369+00:00
-- url     : https://prove2.me/theorems/63f3b177-6909-4d79-9d92-068edd8ffdb7
-- title:
--   P2 M ZMod snd comp chinese Remainder  e253f5662d04: P2 M ZMod snd comp chinese Remainder  e253f5662d04
-- statement:
--   The P2 M ZMod snd comp chinese Remainder  e253f5662d04 construction uses the P2 M ZMod snd comp chinese Remainder  e253f5662d04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L36-L39
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L36-L39

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_snd_comp_chineseRemainder__e253f5662d04 {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.snd (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      unitsMap (dvd_mul_left n m) := by sorry

alias «ZMod».«snd_comp_chineseRemainderₓ» := P2M_ZMod_snd_comp_chineseRemainder__e253f5662d04
