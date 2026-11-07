-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_0
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:07.510007+00:00
-- url     : https://prove2.me/theorems/37cfe0a0-123c-4ed6-a592-6d34cffb65b4
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 0
-- statement:
--   Quadratic coefficient certificate with fixed first index 0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L60-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L60-L74

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_0 (right : Fin 10)
    (hlt : (0 : Fin 10) < right) :
    sourcePairCoefficient 0 right = quadraticGateCoefficient 0 right := by sorry
