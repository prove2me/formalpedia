-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:46:39.838311+00:00
-- url     : https://prove2.me/theorems/7a5845e3-ee1d-428c-8686-83ff0b8067ba
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 7
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L58-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L58-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_7 (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 0 7 third = cubicGateCoefficient 0 7 third := by sorry
