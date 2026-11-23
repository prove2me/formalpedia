-- Prove2me | Theorems.Thm_P2M_Stream__extract_eq_ofFn_8231fd1645c4
-- name    : P2M_Stream__extract_eq_ofFn_8231fd1645c4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:42.32728+00:00
-- url     : https://prove2.me/theorems/c5710840-5d55-4d75-ae5a-90544d385da7
-- title:
--   P2 M Stream  extract eq of Fn 8231fd1645c4: P2 M Stream  extract eq of Fn 8231fd1645c4
-- statement:
--   The P2 M Stream  extract eq of Fn 8231fd1645c4 construction uses the P2 M Stream  extract eq of Fn 8231fd1645c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L75-L79
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L75-L79

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_eq_ofFn_8231fd1645c4 {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by sorry

alias «Stream'».«extract_eq_ofFn» := P2M_Stream__extract_eq_ofFn_8231fd1645c4
