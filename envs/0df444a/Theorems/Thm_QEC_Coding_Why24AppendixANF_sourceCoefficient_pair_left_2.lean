-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_2
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:12.525306+00:00
-- url     : https://prove2.me/theorems/6ddcc84a-ead5-4b78-a5eb-f8e24917a3f7
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 2
-- statement:
--   Quadratic coefficient certificate with fixed first index 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L108-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L108-L124

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_2 (right : Fin 10)
    (hlt : (2 : Fin 10) < right) :
    sourcePairCoefficient 2 right = quadraticGateCoefficient 2 right := by sorry
