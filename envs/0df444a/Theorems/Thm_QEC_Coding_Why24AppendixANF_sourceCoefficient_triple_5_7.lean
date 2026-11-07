-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_5_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:55:42.817096+00:00
-- url     : https://prove2.me/theorems/fe5d9a18-4839-4c52-ba26-df2d269b1257
-- title:
--   Why24 Appendix ANF: source Coefficient triple 5 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 5, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L58-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L58-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 5 7 third = cubicGateCoefficient 5 7 third := by sorry
