-- Prove2me | Theorems.Thm_P2M_Stream__get_drop__05b839498f63
-- name    : P2M_Stream__get_drop__05b839498f63
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:07.071177+00:00
-- url     : https://prove2.me/theorems/027ef991-9852-4f59-9d9e-71a135cfa0d9
-- title:
--   P2 M Stream  get drop  05b839498f63: P2 M Stream  get drop  05b839498f63
-- statement:
--   The P2 M Stream  get drop  05b839498f63 construction uses the P2 M Stream  get drop  05b839498f63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L53-L55
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L53-L55

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__get_drop__05b839498f63 {xs : Stream' X} {n k : ℕ} :
    (xs.drop n) k = xs (n + k) := by sorry

alias «Stream'».«get_drop'» := P2M_Stream__get_drop__05b839498f63
