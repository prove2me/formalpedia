-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:50.489388+00:00
-- url     : https://prove2.me/theorems/972b3db9-6322-4e58-82b3-dc25ff156011
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 6
-- statement:
--   Quadratic coefficient certificate with fixed first index 6.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L87-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L87-L107

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_6 (right : Fin 10)
    (hlt : (6 : Fin 10) < right) :
    sourcePairCoefficient 6 right = quadraticGateCoefficient 6 right := by sorry
