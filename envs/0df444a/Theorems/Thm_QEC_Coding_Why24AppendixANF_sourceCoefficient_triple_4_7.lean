-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:54:51.989814+00:00
-- url     : https://prove2.me/theorems/ae98ee80-8953-4e09-ba74-e73810f5f8fd
-- title:
--   Why24 Appendix ANF: source Coefficient triple 4 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 4, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L100-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L100-L121

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 4 7 third = cubicGateCoefficient 4 7 third := by sorry
