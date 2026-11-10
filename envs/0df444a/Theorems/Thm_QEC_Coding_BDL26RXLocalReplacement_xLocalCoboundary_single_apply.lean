-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalCoboundary_single_apply
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalCoboundary_single_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:20:57.019969+00:00
-- url     : https://prove2.me/theorems/4a3a4e62-77f2-4107-8cc1-d1a1312d7c70
-- title:
--   BDL26 RXLocal Replacement: x Local Coboundary single apply
-- statement:
--   Coordinate formula for a singleton local correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L252-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L252-L263

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalCoboundary_single_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) (b : Field) (face : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) (Pi.single edge b) face =
      b * doubleCylinderFaceEdgeMatrix P x S edge face := by sorry
