-- Prove2me | Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
-- name    : P2M_Stream__append_extract_drop_29d8f2c46a9f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:11.244873+00:00
-- url     : https://prove2.me/theorems/4482573f-f5ff-419a-af94-2b7f23306770
-- title:
--   P2 M Stream  append extract drop 29d8f2c46a9f: P2 M Stream  append extract drop 29d8f2c46a9f
-- statement:
--   The P2 M Stream  append extract drop 29d8f2c46a9f construction uses the P2 M Stream  append extract drop 29d8f2c46a9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L93-L95
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L93-L95

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__append_extract_drop_29d8f2c46a9f {xs : Stream' X} {n : ℕ} :
    (xs.extract 0 n) ++ₛ (xs.drop n) = xs := by sorry

alias «Stream'».«append_extract_drop» := P2M_Stream__append_extract_drop_29d8f2c46a9f
