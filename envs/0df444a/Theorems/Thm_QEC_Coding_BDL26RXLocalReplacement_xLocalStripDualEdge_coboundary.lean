-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripDualEdge_coboundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:26:57.798347+00:00
-- url     : https://prove2.me/theorems/36a1934f-e30d-4e30-a3f7-e7e8419669b6
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Dual Edge coboundary
-- statement:
--   Exact two-rectangle coboundary of an internal strip correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L644-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L644-L655

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (edge : StripEdge S.half) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalStripDualEdge P x S face side edge) b) =
      Pi.single (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripStart S.half edge))) b +
      Pi.single (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripEnd S.half edge))) b := by sorry
