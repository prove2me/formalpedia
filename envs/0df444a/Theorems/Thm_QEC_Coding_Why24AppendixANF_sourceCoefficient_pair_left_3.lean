-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_3
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:16.250998+00:00
-- url     : https://prove2.me/theorems/e42d1d52-b33c-40a4-acb4-5777df5a3fb6
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 3
-- statement:
--   Quadratic coefficient certificate with fixed first index 3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L70-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L70-L87

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_3 (right : Fin 10)
    (hlt : (3 : Fin 10) < right) :
    sourcePairCoefficient 3 right = quadraticGateCoefficient 3 right := by sorry
