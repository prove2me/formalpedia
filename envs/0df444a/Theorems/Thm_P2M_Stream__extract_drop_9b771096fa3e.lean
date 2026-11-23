-- Prove2me | Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
-- name    : P2M_Stream__extract_drop_9b771096fa3e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:07.80919+00:00
-- url     : https://prove2.me/theorems/538e5012-5e53-468d-b4be-2a93fa01c4a7
-- title:
--   P2 M Stream  extract drop 9b771096fa3e: P2 M Stream  extract drop 9b771096fa3e
-- statement:
--   The P2 M Stream  extract drop 9b771096fa3e construction uses the P2 M Stream  extract drop 9b771096fa3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L107-L110
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L107-L110

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_drop_9b771096fa3e {xs : Stream' X} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by sorry

alias «Stream'».«extract_drop» := P2M_Stream__extract_drop_9b771096fa3e
