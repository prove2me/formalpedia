-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:06:03.540649+00:00
-- url     : https://prove2.me/theorems/31ff8384-abcc-4e6c-8415-d87245cf22c4
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L25-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L25-L45

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 2 6 third = cubicGateCoefficient 2 6 third := by sorry
