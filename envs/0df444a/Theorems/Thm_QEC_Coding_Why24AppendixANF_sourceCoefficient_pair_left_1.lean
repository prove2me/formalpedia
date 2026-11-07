-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_1
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:17.927575+00:00
-- url     : https://prove2.me/theorems/42e39d22-168c-414c-aa18-ee04fdc40796
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 1
-- statement:
--   Quadratic coefficient certificate with fixed first index 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L90-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L90-L105

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_1 (right : Fin 10)
    (hlt : (1 : Fin 10) < right) :
    sourcePairCoefficient 1 right = quadraticGateCoefficient 1 right := by sorry
