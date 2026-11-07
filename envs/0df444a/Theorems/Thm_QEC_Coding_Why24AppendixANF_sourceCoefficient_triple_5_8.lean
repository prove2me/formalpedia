-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_5_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:56:05.421886+00:00
-- url     : https://prove2.me/theorems/64d7c1c3-456f-4251-baa4-68da77ae6972
-- title:
--   Why24 Appendix ANF: source Coefficient triple 5 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 5, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L87-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L87-L109

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 5 8 third = cubicGateCoefficient 5 8 third := by sorry
