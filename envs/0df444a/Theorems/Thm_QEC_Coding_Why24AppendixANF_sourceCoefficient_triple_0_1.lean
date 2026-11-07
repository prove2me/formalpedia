-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:43:32.222318+00:00
-- url     : https://prove2.me/theorems/2ff28215-5d7a-4426-ba47-6c85cee3c248
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 1
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L50-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L50-L65

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1 (third : Fin 10)
    (hlt : (1 : Fin 10) < third) :
    sourceTripleCoefficient 0 1 third = cubicGateCoefficient 0 1 third := by sorry
