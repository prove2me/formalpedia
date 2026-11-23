-- Prove2me | Theorems.Thm_P2M_Stream__extract_extract2__d35761143a43
-- name    : P2M_Stream__extract_extract2__d35761143a43
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:16:48.188955+00:00
-- url     : https://prove2.me/theorems/511d0765-6991-411d-a78d-6770e6d794de
-- title:
--   P2 M Stream  extract extract2  d35761143a43: P2 M Stream  extract extract2  d35761143a43
-- statement:
--   The P2 M Stream  extract extract2  d35761143a43 construction uses the P2 M Stream  extract extract2  d35761143a43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L148-L153
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L148-L153

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}

theorem P2M_Stream__extract_extract2__d35761143a43 {xs : Stream' X} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by sorry

alias «Stream'».«extract_extract2'» := P2M_Stream__extract_extract2__d35761143a43
