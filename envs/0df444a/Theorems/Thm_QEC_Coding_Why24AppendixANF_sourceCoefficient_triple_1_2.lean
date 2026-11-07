-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:47:29.742212+00:00
-- url     : https://prove2.me/theorems/b7352cb4-8657-474e-aeec-dc9bcf018832
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 2
-- statement:
--   Cubic coefficient certificate with fixed first indices 1, 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part05.lean#L45-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part05.lean#L45-L61

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part05
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_2 (third : Fin 10)
    (hlt : (2 : Fin 10) < third) :
    sourceTripleCoefficient 1 2 third = cubicGateCoefficient 1 2 third := by sorry
