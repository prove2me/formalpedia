-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:49:21.490985+00:00
-- url     : https://prove2.me/theorems/b1a46d3e-72e5-489b-8dde-7cb42b1ab1ef
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 4
-- statement:
--   Cubic coefficient certificate with fixed first indices 1, 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L35-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L35-L53

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4 (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 1 4 third = cubicGateCoefficient 1 4 third := by sorry
