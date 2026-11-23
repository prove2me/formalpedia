-- Prove2me | Theorems.Thm_P2M_Stream__get_extract_66835107dc16
-- name    : P2M_Stream__get_extract_66835107dc16
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:16.820924+00:00
-- url     : https://prove2.me/theorems/867c5553-0cd8-48a5-8048-0eab0e30ff89
-- title:
--   P2 M Stream  get extract 66835107dc16: P2 M Stream  get extract 66835107dc16
-- statement:
--   The P2 M Stream  get extract 66835107dc16 construction uses the P2 M Stream  get extract 66835107dc16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L125-L127
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L125-L127

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__get_extract_66835107dc16 {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs.get (m + k) := by sorry

alias «Stream'».«get_extract» := P2M_Stream__get_extract_66835107dc16
