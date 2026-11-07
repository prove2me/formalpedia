-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:54.739439+00:00
-- url     : https://prove2.me/theorems/22990a45-9ce3-4b6a-bc57-33f4584e23c1
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 5
-- statement:
--   Quadratic coefficient certificate with fixed first index 5.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L65-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L65-L84

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_5 (right : Fin 10)
    (hlt : (5 : Fin 10) < right) :
    sourcePairCoefficient 5 right = quadraticGateCoefficient 5 right := by sorry
