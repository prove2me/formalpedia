-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_ordered
-- name    : QEC.Coding.Why24AppendixANF.quadraticGatePairs_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:54.895709+00:00
-- url     : https://prove2.me/theorems/80bf0bf2-49eb-426b-9cd6-1e926f8d3c8d
-- title:
--   Why24 Appendix ANF: quadratic Gate Pairs ordered
-- statement:
--   Every printed quadratic pair is in increasing order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L22-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L22-L27

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.quadraticGatePairs_ordered (pair : Fin 10 × Fin 10)
    (hpair : pair ∈ quadraticGatePairs) : pair.1 < pair.2 := by sorry
