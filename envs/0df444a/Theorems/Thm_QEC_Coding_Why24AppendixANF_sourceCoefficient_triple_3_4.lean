-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:52:26.58164+00:00
-- url     : https://prove2.me/theorems/57ca43ee-a13c-49f0-8a72-96cd093a3440
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 4
-- statement:
--   Cubic coefficient certificate with fixed first indices 3, 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L35-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L35-L53

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4 (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 3 4 third = cubicGateCoefficient 3 4 third := by sorry
