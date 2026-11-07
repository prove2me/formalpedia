-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:54:58.704294+00:00
-- url     : https://prove2.me/theorems/5ab5727a-f8fc-4293-a993-957a0719ac85
-- title:
--   Why24 Appendix ANF: source Coefficient triple 4 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 4, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L129-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L129-L151

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 4 8 third = cubicGateCoefficient 4 8 third := by sorry
