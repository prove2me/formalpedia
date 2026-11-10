-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_apply
-- name    : QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:09:24.202574+00:00
-- url     : https://prove2.me/theorems/cf448555-aed2-4300-a85f-7315a2d59ce1
-- title:
--   BDL26 RXLocal Replacement: q Local Coboundary apply
-- statement:
--   The actual Q-block coboundary evaluates as the sum of endpoint bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L61-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L61-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.qLocalCoboundary_apply (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (edge : QDoubleCylinderEdge P q S) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f edge =
      f (qDoubleCylinderEdgeStart P q S edge) +
        f (qDoubleCylinderEdgeEnd P q S edge) := by sorry
