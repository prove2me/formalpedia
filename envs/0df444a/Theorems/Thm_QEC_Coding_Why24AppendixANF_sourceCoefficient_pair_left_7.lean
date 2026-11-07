-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:46.705852+00:00
-- url     : https://prove2.me/theorems/b738d797-4eac-46ab-9ab5-98cd3143c25e
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 7
-- statement:
--   Quadratic coefficient certificate with fixed first index 7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L110-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L110-L131

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_7 (right : Fin 10)
    (hlt : (7 : Fin 10) < right) :
    sourcePairCoefficient 7 right = quadraticGateCoefficient 7 right := by sorry
