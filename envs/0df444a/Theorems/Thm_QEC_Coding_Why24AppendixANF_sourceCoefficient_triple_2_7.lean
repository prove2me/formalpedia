-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:05:28.79316+00:00
-- url     : https://prove2.me/theorems/c782d27e-dab5-4f49-91fd-b0fd40cea744
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L58-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L58-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 2 7 third = cubicGateCoefficient 2 7 third := by sorry
