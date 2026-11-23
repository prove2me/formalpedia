-- Prove2me | Theorems.Thm_P2M_Stream__drop_append_of_ge_length_8fcd0b978030
-- name    : P2M_Stream__drop_append_of_ge_length_8fcd0b978030
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:20:55.71479+00:00
-- url     : https://prove2.me/theorems/f120bf86-463b-45cb-9a43-23abfd5293b5
-- title:
--   P2 M Stream  drop append of ge length 8fcd0b978030: P2 M Stream  drop append of ge length 8fcd0b978030
-- statement:
--   The P2 M Stream  drop append of ge length 8fcd0b978030 construction uses the P2 M Stream  drop append of ge length 8fcd0b978030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L66-L69
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L66-L69

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__drop_append_of_ge_length_8fcd0b978030 {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).drop n = xs.drop (n - xl.length) := by sorry

alias «Stream'».«drop_append_of_ge_length» := P2M_Stream__drop_append_of_ge_length_8fcd0b978030
