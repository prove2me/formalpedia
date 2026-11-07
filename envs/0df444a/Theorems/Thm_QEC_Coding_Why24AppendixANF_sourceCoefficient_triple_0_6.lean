-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:46:02.934904+00:00
-- url     : https://prove2.me/theorems/18b51c88-8921-4d72-810c-9d282de1128c
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L25-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L25-L45

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 0 6 third = cubicGateCoefficient 0 6 third := by sorry
