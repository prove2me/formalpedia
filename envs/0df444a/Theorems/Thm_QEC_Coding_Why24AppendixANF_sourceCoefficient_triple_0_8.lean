-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:46:47.387401+00:00
-- url     : https://prove2.me/theorems/5d20f28a-dfc9-4bf9-ae58-5eb2529196b6
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L87-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L87-L109

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 0 8 third = cubicGateCoefficient 0 8 third := by sorry
