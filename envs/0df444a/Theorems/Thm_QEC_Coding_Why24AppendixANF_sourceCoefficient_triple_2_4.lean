-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:03:52.478534+00:00
-- url     : https://prove2.me/theorems/0c1542cf-1e29-4367-aa9c-29ba11b6bac6
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 4
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L35-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L35-L53

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part10
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_4 (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 2 4 third = cubicGateCoefficient 2 4 third := by sorry
