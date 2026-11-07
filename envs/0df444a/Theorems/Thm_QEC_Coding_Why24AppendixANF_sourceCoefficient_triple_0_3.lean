-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:45:07.445264+00:00
-- url     : https://prove2.me/theorems/bfa3536c-53cc-4f22-9374-b8955842934f
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 3
-- statement:
--   Cubic coefficient certificate with fixed first indices 0, 3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part02.lean#L40-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part02.lean#L40-L57

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3 (third : Fin 10)
    (hlt : (3 : Fin 10) < third) :
    sourceTripleCoefficient 0 3 third = cubicGateCoefficient 0 3 third := by sorry
