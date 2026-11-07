-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_7_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_7_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:25.371073+00:00
-- url     : https://prove2.me/theorems/7c8d99f4-0444-45b9-b933-7721b44b29db
-- title:
--   Why24 Appendix ANF: source Coefficient triple 7 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 7, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L181-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L181-L203

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_7_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 7 8 third = cubicGateCoefficient 7 8 third := by sorry
