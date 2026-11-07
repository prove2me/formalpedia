-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:42:02.84749+00:00
-- url     : https://prove2.me/theorems/ccab0cc6-196c-4e4e-a4b9-729e9247135c
-- title:
--   Why24 Appendix ANF: source Coefficient pair
-- statement:
--   Every normalized quadratic source coefficient equals the literal gate-list
--   coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/Certificate.lean#L20-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/Certificate.lean#L20-L33

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair (left right : Fin 10) (hlt : left < right) :
    sourcePairCoefficient left right = quadraticGateCoefficient left right := by sorry
