-- Prove2me | Theorems.Thm_P2M_Stream__extract_succ_right_19be47645cc9
-- name    : P2M_Stream__extract_succ_right_19be47645cc9
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:18.1978+00:00
-- url     : https://prove2.me/theorems/cab36b41-c1b8-4dce-9079-5237cae1140d
-- title:
--   P2 M Stream  extract succ right 19be47645cc9: P2 M Stream  extract succ right 19be47645cc9
-- statement:
--   The P2 M Stream  extract succ right 19be47645cc9 construction uses the P2 M Stream  extract succ right 19be47645cc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L139-L142
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L139-L142

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_succ_right_19be47645cc9 {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs.get n] := by sorry

alias «Stream'».«extract_succ_right» := P2M_Stream__extract_succ_right_19be47645cc9
