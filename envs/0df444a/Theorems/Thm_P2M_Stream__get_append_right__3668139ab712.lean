-- Prove2me | Theorems.Thm_P2M_Stream__get_append_right__3668139ab712
-- name    : P2M_Stream__get_append_right__3668139ab712
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:14:38.842215+00:00
-- url     : https://prove2.me/theorems/e57d883a-7c61-48fb-b249-4e21f3d9c80a
-- title:
--   P2 M Stream  get append right  3668139ab712: P2 M Stream  get append right  3668139ab712
-- statement:
--   The P2 M Stream  get append right  3668139ab712 construction uses the P2 M Stream  get append right  3668139ab712 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L61-L64
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L61-L64

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__get_append_right__3668139ab712 {xl : List X} {xs : Stream' X} {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ₛ xs) k = xs (k - xl.length) := by sorry

alias «Stream'».«get_append_right'» := P2M_Stream__get_append_right__3668139ab712
