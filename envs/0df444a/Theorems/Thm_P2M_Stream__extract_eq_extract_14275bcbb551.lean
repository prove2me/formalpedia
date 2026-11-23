-- Prove2me | Theorems.Thm_P2M_Stream__extract_eq_extract_14275bcbb551
-- name    : P2M_Stream__extract_eq_extract_14275bcbb551
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:15.227704+00:00
-- url     : https://prove2.me/theorems/71856753-0f18-4e13-b2b9-1572e0d297f3
-- title:
--   P2 M Stream  extract eq extract 14275bcbb551: P2 M Stream  extract eq extract 14275bcbb551
-- statement:
--   The P2 M Stream  extract eq extract 14275bcbb551 construction uses the P2 M Stream  extract eq extract 14275bcbb551 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L81-L87
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L81-L87

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_eq_extract_14275bcbb551 {xs xs' : Stream' X} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by sorry

alias «Stream'».«extract_eq_extract» := P2M_Stream__extract_eq_extract_14275bcbb551
