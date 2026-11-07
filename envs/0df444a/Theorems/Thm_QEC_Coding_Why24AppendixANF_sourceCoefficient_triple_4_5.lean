-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:54:08.292711+00:00
-- url     : https://prove2.me/theorems/50745361-5ba5-47ff-b293-8f9d4d560b8d
-- title:
--   Why24 Appendix ANF: source Coefficient triple 4 5
-- statement:
--   Cubic coefficient certificate with fixed first indices 4, 5.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L30-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L30-L49

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_5 (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 4 5 third = cubicGateCoefficient 4 5 third := by sorry
