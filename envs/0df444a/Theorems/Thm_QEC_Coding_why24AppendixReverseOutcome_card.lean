-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixReverseOutcome_card
-- name    : QEC.Coding.why24AppendixReverseOutcome_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:41:35.721405+00:00
-- url     : https://prove2.me/theorems/16686558-141b-44a0-bf28-e6ba8aee38af
-- title:
--   Coding: why24 Appendix Reverse Outcome card
-- statement:
--   The reverse conversion has exactly `2^7 = 128` measurement outcomes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L38-L41

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24AppendixReverseOutcome_card :
    Fintype.card Why24AppendixReverseOutcome = 128 := by sorry
