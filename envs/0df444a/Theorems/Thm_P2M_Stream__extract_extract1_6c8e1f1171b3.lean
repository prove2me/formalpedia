-- Prove2me | Theorems.Thm_P2M_Stream__extract_extract1_6c8e1f1171b3
-- name    : P2M_Stream__extract_extract1_6c8e1f1171b3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:33.97694+00:00
-- url     : https://prove2.me/theorems/da345a9a-3b7c-4c83-a3f4-7b7828306912
-- title:
--   P2 M Stream  extract extract1 6c8e1f1171b3: P2 M Stream  extract extract1 6c8e1f1171b3
-- statement:
--   The P2 M Stream  extract extract1 6c8e1f1171b3 construction uses the P2 M Stream  extract extract1 6c8e1f1171b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L159-L161
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L159-L161

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_extract1_6c8e1f1171b3 {xs : Stream' X} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by sorry

alias «Stream'».«extract_extract1» := P2M_Stream__extract_extract1_6c8e1f1171b3
