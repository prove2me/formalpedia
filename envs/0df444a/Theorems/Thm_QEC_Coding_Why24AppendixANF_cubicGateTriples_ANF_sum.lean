-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_cubicGateTriples_ANF_sum
-- name    : QEC.Coding.Why24AppendixANF.cubicGateTriples_ANF_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:32.685291+00:00
-- url     : https://prove2.me/theorems/7dbd08f9-e009-4903-92dd-e4b78657f149
-- title:
--   Why24 Appendix ANF: cubic Gate Triples ANF sum
-- statement:
--   The printed cubic list sums to its normalized sparse ANF slice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Certificate.lean#L82-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Certificate.lean#L82-L99

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.cubicGateTriples_ANF_sum :
    (cubicGateTriples.map
      (fun triple => generator triple.1 * generator triple.2.1 *
        generator triple.2.2)).sum =
      ∑ triple : Fin 10 × Fin 10 × Fin 10,
        if triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 then
          cubicGateCoefficient triple.1 triple.2.1 triple.2.2 •
            (generator triple.1 * generator triple.2.1 *
              generator triple.2.2)
        else 0 := by sorry
