-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:53:31.289988+00:00
-- url     : https://prove2.me/theorems/a2539d24-5ea0-4d96-a48e-bed00325d991
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 3, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part13.lean#L58-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part13.lean#L58-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part13
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 3 7 third = cubicGateCoefficient 3 7 third := by sorry
