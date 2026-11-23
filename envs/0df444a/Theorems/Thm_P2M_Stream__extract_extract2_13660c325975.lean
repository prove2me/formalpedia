-- Prove2me | Theorems.Thm_P2M_Stream__extract_extract2_13660c325975
-- name    : P2M_Stream__extract_extract2_13660c325975
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:25.646536+00:00
-- url     : https://prove2.me/theorems/2a9161ac-cffd-4392-89b3-d2035d31c12a
-- title:
--   P2 M Stream  extract extract2 13660c325975: P2 M Stream  extract extract2 13660c325975
-- statement:
--   The P2 M Stream  extract extract2 13660c325975 construction uses the P2 M Stream  extract extract2 13660c325975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L155-L157
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L155-L157

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_extract2_13660c325975 {xs : Stream' X} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by sorry

alias «Stream'».«extract_extract2» := P2M_Stream__extract_extract2_13660c325975
