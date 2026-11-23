-- Prove2me | Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
-- name    : P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:18.740686+00:00
-- url     : https://prove2.me/theorems/cd5f749a-69fd-4c7c-b732-92a29ecaf162
-- title:
--   P2 M ZMod snd chinese Remainder  54cb5b0df9be: P2 M ZMod snd chinese Remainder  54cb5b0df9be
-- statement:
--   The P2 M ZMod snd chinese Remainder  54cb5b0df9be construction uses the P2 M ZMod snd chinese Remainder  54cb5b0df9be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L32-L34
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L32-L34

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem P2M_ZMod_snd_chineseRemainder__54cb5b0df9be {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).2 = unitsMap (dvd_mul_left n m) x := by sorry

alias «ZMod».«snd_chineseRemainderₓ» := P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
