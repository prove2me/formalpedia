-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_5_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:55:25.020896+00:00
-- url     : https://prove2.me/theorems/d680e340-db09-49ae-b85d-624fefa018a4
-- title:
--   Why24 Appendix ANF: source Coefficient triple 5 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 5, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L25-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L25-L45

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 5 6 third = cubicGateCoefficient 5 6 third := by sorry
