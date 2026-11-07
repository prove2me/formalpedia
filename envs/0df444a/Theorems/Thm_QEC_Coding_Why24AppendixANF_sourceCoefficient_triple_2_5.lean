-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:04:25.146897+00:00
-- url     : https://prove2.me/theorems/72bbdea9-c809-4d26-bdc8-eb775b95dbdc
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 5
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 5.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L76-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L76-L95

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part10
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 2 5 third = cubicGateCoefficient 2 5 third := by sorry
