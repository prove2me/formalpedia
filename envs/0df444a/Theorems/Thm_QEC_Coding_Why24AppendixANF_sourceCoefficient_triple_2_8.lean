-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:05:29.531978+00:00
-- url     : https://prove2.me/theorems/5f493eff-19aa-4449-84dc-fcc4a972b69a
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 2, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L87-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L87-L109

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 2 8 third = cubicGateCoefficient 2 8 third := by sorry
