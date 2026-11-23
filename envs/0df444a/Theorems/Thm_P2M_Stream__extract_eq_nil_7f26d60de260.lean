-- Prove2me | Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260
-- name    : P2M_Stream__extract_eq_nil_7f26d60de260
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:14.951715+00:00
-- url     : https://prove2.me/theorems/ef844f1f-a9af-4e32-8a21-34c3496767c5
-- title:
--   P2 M Stream  extract eq nil 7f26d60de260: P2 M Stream  extract eq nil 7f26d60de260
-- statement:
--   The P2 M Stream  extract eq nil 7f26d60de260 construction uses the P2 M Stream  extract eq nil 7f26d60de260 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L116-L118
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L116-L118

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_eq_nil_7f26d60de260 {xs : Stream' X} {n : ℕ} :
    xs.extract n n = [] := by sorry

alias «Stream'».«extract_eq_nil» := P2M_Stream__extract_eq_nil_7f26d60de260
