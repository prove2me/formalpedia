-- Prove2me | Theorems.Thm_P2M_Stream__extract_eq_nil_iff_c45b6d031ac4
-- name    : P2M_Stream__extract_eq_nil_iff_c45b6d031ac4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:16.306691+00:00
-- url     : https://prove2.me/theorems/c9c8995e-fc21-4ea1-9d7c-50d866a341b5
-- title:
--   P2 M Stream  extract eq nil iff c45b6d031ac4: P2 M Stream  extract eq nil iff c45b6d031ac4
-- statement:
--   The P2 M Stream  extract eq nil iff c45b6d031ac4 construction uses the P2 M Stream  extract eq nil iff c45b6d031ac4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L120-L123
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L120-L123

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_eq_nil_iff_c45b6d031ac4 {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by sorry

alias «Stream'».«extract_eq_nil_iff» := P2M_Stream__extract_eq_nil_iff_c45b6d031ac4
