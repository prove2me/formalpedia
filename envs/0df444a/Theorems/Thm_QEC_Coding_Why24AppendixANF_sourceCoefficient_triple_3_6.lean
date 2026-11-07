-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:53:18.153604+00:00
-- url     : https://prove2.me/theorems/bcb7132d-4cc9-4658-a137-19cbc2dc9908
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 3, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part13.lean#L25-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part13.lean#L25-L45

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part13
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 3 6 third = cubicGateCoefficient 3 6 third := by sorry
