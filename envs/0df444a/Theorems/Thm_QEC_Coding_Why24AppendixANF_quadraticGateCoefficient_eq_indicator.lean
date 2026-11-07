-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGateCoefficient_eq_indicator
-- name    : QEC.Coding.Why24AppendixANF.quadraticGateCoefficient_eq_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:08:09.693652+00:00
-- url     : https://prove2.me/theorems/6b19c657-204c-49b7-aff6-60fec8dbf912
-- title:
--   Why24 Appendix ANF: quadratic Gate Coefficient eq indicator
-- statement:
--   The quadratic coefficient is the membership indicator of the printed
--   pair list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L31-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L31-L33

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.quadraticGateCoefficient_eq_indicator (pair : Fin 10 × Fin 10) :
    quadraticGateCoefficient pair.1 pair.2 =
      if pair ∈ quadraticGatePairs then 1 else 0 := by sorry
