-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:00.493763+00:00
-- url     : https://prove2.me/theorems/536e24e7-1c22-41a5-938e-0d42d8dd1429
-- title:
--   Why24 Appendix ANF: source Coefficient pair left 8
-- statement:
--   Quadratic coefficient certificate with fixed first index 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L134-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L134-L156

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_8 (right : Fin 10)
    (hlt : (8 : Fin 10) < right) :
    sourcePairCoefficient 8 right = quadraticGateCoefficient 8 right := by sorry
