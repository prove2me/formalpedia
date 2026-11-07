-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:50:05.722267+00:00
-- url     : https://prove2.me/theorems/c152fb79-249f-4774-8c5d-f55a46c19735
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 6
-- statement:
--   Cubic coefficient certificate with fixed first indices 1, 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L25-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L25-L45

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part08
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_6 (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 1 6 third = cubicGateCoefficient 1 6 third := by sorry
