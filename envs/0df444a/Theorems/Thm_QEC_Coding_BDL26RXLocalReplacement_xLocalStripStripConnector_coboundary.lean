-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripStripConnector_coboundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:11.301561+00:00
-- url     : https://prove2.me/theorems/d69080ff-d301-45b6-a1e0-1fe35307afdb
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Strip Connector coboundary
-- statement:
--   Exact endpoint syndrome of the cost-two connector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L953-L963
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L953-L963

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_coboundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalStripStripConnector P x S face) b) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inr 0)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 1)) b := by sorry
