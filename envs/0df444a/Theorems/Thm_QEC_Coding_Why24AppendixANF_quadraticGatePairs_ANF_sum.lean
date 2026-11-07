-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_ANF_sum
-- name    : QEC.Coding.Why24AppendixANF.quadraticGatePairs_ANF_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:53:02.629311+00:00
-- url     : https://prove2.me/theorems/72f60e2a-3bcb-4e8c-829a-ef05418209ab
-- title:
--   Why24 Appendix ANF: quadratic Gate Pairs ANF sum
-- statement:
--   The printed quadratic list sums to its normalized sparse ANF slice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Certificate.lean#L67-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Certificate.lean#L67-L79

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.quadraticGatePairs_ANF_sum :
    (quadraticGatePairs.map
      (fun pair => generator pair.1 * generator pair.2)).sum =
      ∑ pair : Fin 10 × Fin 10, if pair.1 < pair.2 then
        quadraticGateCoefficient pair.1 pair.2 •
          (generator pair.1 * generator pair.2)
      else 0 := by sorry
