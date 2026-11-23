-- Prove2me | Theorems.Thm_P2M_Stream__extract_succ_right__dce2e16ca09b
-- name    : P2M_Stream__extract_succ_right__dce2e16ca09b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:24.46761+00:00
-- url     : https://prove2.me/theorems/c51bc971-ac22-49f1-9735-1bd044df4faa
-- title:
--   P2 M Stream  extract succ right  dce2e16ca09b: P2 M Stream  extract succ right  dce2e16ca09b
-- statement:
--   The P2 M Stream  extract succ right  dce2e16ca09b construction uses the P2 M Stream  extract succ right  dce2e16ca09b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L144-L146
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L144-L146

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_succ_right__dce2e16ca09b {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by sorry

alias «Stream'».«extract_succ_right'» := P2M_Stream__extract_succ_right__dce2e16ca09b
