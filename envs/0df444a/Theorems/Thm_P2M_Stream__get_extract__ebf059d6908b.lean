-- Prove2me | Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
-- name    : P2M_Stream__get_extract__ebf059d6908b
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:11:13.805018+00:00
-- url     : https://prove2.me/theorems/f48894fb-4340-4867-b082-f38a59fde1ab
-- title:
--   P2 M Stream  get extract  ebf059d6908b: P2 M Stream  get extract  ebf059d6908b
-- statement:
--   The P2 M Stream  get extract  ebf059d6908b construction uses the P2 M Stream  get extract  ebf059d6908b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L129-L131
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L129-L131

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__get_extract__ebf059d6908b {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs (m + k) := by sorry

alias «Stream'».«get_extract'» := P2M_Stream__get_extract__ebf059d6908b
