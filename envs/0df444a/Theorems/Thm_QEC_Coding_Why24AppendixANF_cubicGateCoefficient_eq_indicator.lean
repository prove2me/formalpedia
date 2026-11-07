-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_cubicGateCoefficient_eq_indicator
-- name    : QEC.Coding.Why24AppendixANF.cubicGateCoefficient_eq_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:05.29019+00:00
-- url     : https://prove2.me/theorems/704b1da8-efa1-4411-b47a-a55c10d1e4c3
-- title:
--   Why24 Appendix ANF: cubic Gate Coefficient eq indicator
-- statement:
--   The cubic coefficient is the membership indicator of the printed triple
--   list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L50-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L50-L53

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.cubicGateCoefficient_eq_indicator
    (triple : Fin 10 × Fin 10 × Fin 10) :
    cubicGateCoefficient triple.1 triple.2.1 triple.2.2 =
      if triple ∈ cubicGateTriples then 1 else 0 := by sorry
