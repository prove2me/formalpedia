-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_6_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_6_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:56:46.444604+00:00
-- url     : https://prove2.me/theorems/5076e41c-80d8-42f7-899b-fea86e6a7999
-- title:
--   Why24 Appendix ANF: source Coefficient triple 6 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 6, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L122-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L122-L143

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_6_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 6 7 third = cubicGateCoefficient 6 7 third := by sorry
