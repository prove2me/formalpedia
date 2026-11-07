-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:54:26.992702+00:00
-- url     : https://prove2.me/theorems/be0d67fa-b4e9-447c-b1da-d2cf0178af11
-- title:
--   Why24 Appendix ANF: source Coefficient triple 4 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 4, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L67-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L67-L87

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 4 6 third = cubicGateCoefficient 4 6 third := by sorry
