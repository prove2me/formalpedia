-- Prove2me | Theorems.Thm_P2M_Stream__extract_eq_take_3a08a50f66bd
-- name    : P2M_Stream__extract_eq_take_3a08a50f66bd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:17.541026+00:00
-- url     : https://prove2.me/theorems/028830f0-8711-4f17-a487-17d26afb1b94
-- title:
--   P2 M Stream  extract eq take 3a08a50f66bd: P2 M Stream  extract eq take 3a08a50f66bd
-- statement:
--   The P2 M Stream  extract eq take 3a08a50f66bd construction uses the P2 M Stream  extract eq take 3a08a50f66bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L89-L91
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L89-L91

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_eq_take_3a08a50f66bd {xs : Stream' X} {n : ℕ} :
    xs.extract 0 n = xs.take n := by sorry

alias «Stream'».«extract_eq_take» := P2M_Stream__extract_eq_take_3a08a50f66bd
