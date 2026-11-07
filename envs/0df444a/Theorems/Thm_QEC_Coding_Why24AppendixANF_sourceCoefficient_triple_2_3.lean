-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:51:38.373022+00:00
-- url     : https://prove2.me/theorems/d1ccab67-006d-40ff-b592-9f59480e63e4
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 3
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L40-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L40-L57

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3 (third : Fin 10)
    (hlt : (3 : Fin 10) < third) :
    sourceTripleCoefficient 2 3 third = cubicGateCoefficient 2 3 third := by sorry
