-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_add_constant
-- name    : QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_add_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:10:59.335695+00:00
-- url     : https://prove2.me/theorems/9b3892fc-8672-4c42-8aee-dd63bbcd0406
-- title:
--   BDL26 RXLocal Replacement: q Local Coboundary add constant
-- statement:
--   A constant binary translation preserves the entire Q-local syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L71-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L71-L78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_add_constant (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S)) (a : Field) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => f v + a) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f := by sorry
