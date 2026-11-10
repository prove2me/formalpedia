-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalLayerStripConnector_coboundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalLayerStripConnector_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:59.253195+00:00
-- url     : https://prove2.me/theorems/4058b07a-50ef-41f6-9151-2665c2b3e963
-- title:
--   BDL26 RXLocal Replacement: x Local Layer Strip Connector coboundary
-- statement:
--   Exact endpoint syndrome of each cost-one connector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L830-L839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L830-L839

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalLayerStripConnector_coboundary
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalLayerStripConnector P x S face copy side) b) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inl copy)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr side)) b := by sorry
