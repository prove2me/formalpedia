-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:09.866389+00:00
-- url     : https://prove2.me/theorems/5ca5076d-e973-4a0a-8e63-16c32f91e263
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 4
-- statement:
--   Quadratic coefficient certificate with fixed first index 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L90-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L90-L108

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_4 (right : Fin 10)
    (hlt : (4 : Fin 10) < right) :
    sourcePairCoefficient 4 right = quadraticGateCoefficient 4 right := by sorry
