-- Prove2me | Theorems.Thm_P2M_Stream__extract_apppend_right_right_39982fde78ca
-- name    : P2M_Stream__extract_apppend_right_right_39982fde78ca
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:12.30761+00:00
-- url     : https://prove2.me/theorems/a48ecb74-fd7b-4469-95ca-c395db503bfd
-- title:
--   P2 M Stream  extract apppend right right 39982fde78ca: P2 M Stream  extract apppend right right 39982fde78ca
-- statement:
--   The P2 M Stream  extract apppend right right 39982fde78ca construction uses the P2 M Stream  extract apppend right right 39982fde78ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L97-L100
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L97-L100

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_apppend_right_right_39982fde78ca {xl : List X} {xs : Stream' X} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ₛ xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by sorry

alias «Stream'».«extract_apppend_right_right» := P2M_Stream__extract_apppend_right_right_39982fde78ca
