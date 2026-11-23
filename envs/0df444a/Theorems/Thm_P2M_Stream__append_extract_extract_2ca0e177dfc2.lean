-- Prove2me | Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2
-- name    : P2M_Stream__append_extract_extract_2ca0e177dfc2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:15.53473+00:00
-- url     : https://prove2.me/theorems/fd4eb735-f6aa-4556-bf11-10c1e671af0e
-- title:
--   P2 M Stream  append extract extract 2ca0e177dfc2: P2 M Stream  append extract extract 2ca0e177dfc2
-- statement:
--   The P2 M Stream  append extract extract 2ca0e177dfc2 construction uses the P2 M Stream  append extract extract 2ca0e177dfc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L133-L137
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L133-L137

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__append_extract_extract_2ca0e177dfc2 {xs : Stream' X} {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by sorry

alias «Stream'».«append_extract_extract» := P2M_Stream__append_extract_extract_2ca0e177dfc2
