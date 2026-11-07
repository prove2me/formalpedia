-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:46:03.718248+00:00
-- url     : https://prove2.me/theorems/9125ca51-35e0-4975-92c9-0d52589f500c
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 5
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 5.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part03.lean#L76-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part03.lean#L76-L95

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part03
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 0 5 third = cubicGateCoefficient 0 5 third := by sorry
