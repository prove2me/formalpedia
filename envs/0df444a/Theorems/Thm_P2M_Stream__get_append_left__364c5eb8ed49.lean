-- Prove2me | Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
-- name    : P2M_Stream__get_append_left__364c5eb8ed49
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:08.981967+00:00
-- url     : https://prove2.me/theorems/7a003f4a-357e-4b8f-9c67-0e3df249e0b8
-- title:
--   P2 M Stream  get append left  364c5eb8ed49: P2 M Stream  get append left  364c5eb8ed49
-- statement:
--   The P2 M Stream  get append left  364c5eb8ed49 construction uses the P2 M Stream  get append left  364c5eb8ed49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L57-L59
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L57-L59

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__get_append_left__364c5eb8ed49 {xl : List X} {xs : Stream' X} {k : ℕ} (h : k < xl.length) :
    (xl ++ₛ xs) k = xl[k] := by sorry

alias «Stream'».«get_append_left'» := P2M_Stream__get_append_left__364c5eb8ed49
