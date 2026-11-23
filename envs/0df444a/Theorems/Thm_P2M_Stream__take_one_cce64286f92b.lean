-- Prove2me | Theorems.Thm_P2M_Stream__take_one_cce64286f92b
-- name    : P2M_Stream__take_one_cce64286f92b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:07.454806+00:00
-- url     : https://prove2.me/theorems/1957e0bc-f925-49d7-8a4e-1fb0a818b9cc
-- title:
--   P2 M Stream  take one cce64286f92b: P2 M Stream  take one cce64286f92b
-- statement:
--   The P2 M Stream  take one cce64286f92b construction uses the P2 M Stream  take one cce64286f92b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L45-L47
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L45-L47

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__take_one_cce64286f92b {xs : Stream' X} :
    xs.take 1 = [xs.get 0] := by sorry

alias «Stream'».«take_one» := P2M_Stream__take_one_cce64286f92b
