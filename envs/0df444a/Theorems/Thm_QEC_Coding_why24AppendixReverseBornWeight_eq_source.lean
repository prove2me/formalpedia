-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixReverseBornWeight_eq_source
-- name    : QEC.Coding.why24AppendixReverseBornWeight_eq_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:09:09.110092+00:00
-- url     : https://prove2.me/theorems/ca104d14-f220-43c9-9b81-fd542a770fa8
-- title:
--   Coding: why24 Appendix Reverse Born Weight eq source
-- statement:
--   Every one of the 128 source outcomes has Born weight `1/128`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L438-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L438-L443

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24AppendixReverseBornWeight_eq_source
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseBornWeight outcome = (1 / 128 : Real) := by sorry
