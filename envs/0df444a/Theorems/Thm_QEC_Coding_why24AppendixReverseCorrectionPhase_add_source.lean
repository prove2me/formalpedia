-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixReverseCorrectionPhase_add_source
-- name    : QEC.Coding.why24AppendixReverseCorrectionPhase_add_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:52:53.1762+00:00
-- url     : https://prove2.me/theorems/66385125-14ac-45a0-8f4e-a7a324dcea4a
-- title:
--   Coding: why24 Appendix Reverse Correction Phase add source
-- statement:
--   The correction cancels the actual literal source phase and leaves exactly
--   the retained `CCZ` phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L83-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L83-L98

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24AppendixReverseCorrectionPhase_add_source
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseCorrectionPhase outcome retained +
        why24AppendixReverseSourcePhase outcome retained =
      why24CCZPhase retained := by sorry
