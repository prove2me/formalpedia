-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalLayerStripConnector_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalLayerStripConnector_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:51.141875+00:00
-- url     : https://prove2.me/theorems/bcb1b923-3edb-4520-a0e2-8cde0b68552f
-- title:
--   BDL26 RXLocal Replacement: x Local Layer Strip Connector incidence
-- statement:
--   A copied boundary connector joins precisely one grid and one strip root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L805-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L805-L827

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalLayerStripConnector_incidence
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S
        (xLocalLayerStripConnector P x S face copy side) target =
      (if target = xLocalRegionRoot P x S face (Sum.inl copy) then 1 else 0) +
      (if target = xLocalRegionRoot P x S face (Sum.inr side) then 1 else 0) := by sorry
