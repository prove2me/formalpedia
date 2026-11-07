-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:50:36.22561+00:00
-- url     : https://prove2.me/theorems/a44ee66e-f16a-4a81-bc1a-481cbe369864
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 1, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L58-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L58-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part08
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 1 7 third = cubicGateCoefficient 1 7 third := by sorry
