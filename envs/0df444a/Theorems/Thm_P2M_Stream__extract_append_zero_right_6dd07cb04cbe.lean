-- Prove2me | Theorems.Thm_P2M_Stream__extract_append_zero_right_6dd07cb04cbe
-- name    : P2M_Stream__extract_append_zero_right_6dd07cb04cbe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:15:38.922367+00:00
-- url     : https://prove2.me/theorems/47b6f1e0-7c92-4961-93cf-02f27a6945b5
-- title:
--   P2 M Stream  extract append zero right 6dd07cb04cbe: P2 M Stream  extract append zero right 6dd07cb04cbe
-- statement:
--   The P2 M Stream  extract append zero right 6dd07cb04cbe construction uses the P2 M Stream  extract append zero right 6dd07cb04cbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L102-L105
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L102-L105

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_append_zero_right_6dd07cb04cbe {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by sorry

alias «Stream'».«extract_append_zero_right» := P2M_Stream__extract_append_zero_right_6dd07cb04cbe
