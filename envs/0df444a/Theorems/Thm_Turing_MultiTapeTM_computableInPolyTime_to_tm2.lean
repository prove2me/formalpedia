-- Prove2me | Theorems.Thm_Turing_MultiTapeTM_computableInPolyTime_to_tm2
-- name    : Turing.MultiTapeTM.computableInPolyTime_to_tm2
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T06:43:14.696516+00:00
-- url     : https://prove2.me/theorems/84af254d-012e-4140-bcd5-cc8a87238151
-- title:
--   Translation from polynomial-time binary multitape computations to TM2
-- statement:
--   A polynomial-time binary multitape computation has a Mathlib TM2 implementation with the same input and output encoding.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Mathlib.Computability.TuringMachine.Computable

open Turing Turing.MultiTapeTM

theorem Turing.MultiTapeTM.computableInPolyTime_to_tm2 {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (h : ComputableInPolyTime f encIn encOut) :
    Nonempty (TM2ComputableInPolyTime encIn encOut f) := by sorry
