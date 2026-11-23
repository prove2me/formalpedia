-- Prove2me | Theorems.Thm_P2M_Stream__take_one__38ffcc18b2b5
-- name    : P2M_Stream__take_one__38ffcc18b2b5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:56.230312+00:00
-- url     : https://prove2.me/theorems/266770e4-edb0-48f8-b074-bd398f5e624e
-- title:
--   P2 M Stream  take one  38ffcc18b2b5: P2 M Stream  take one  38ffcc18b2b5
-- statement:
--   The P2 M Stream  take one  38ffcc18b2b5 construction uses the P2 M Stream  take one  38ffcc18b2b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L49-L51
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L49-L51

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__take_one__38ffcc18b2b5 {xs : Stream' X} :
    xs.take 1 = [xs 0] := by sorry

alias «Stream'».«take_one'» := P2M_Stream__take_one__38ffcc18b2b5
