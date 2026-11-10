-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripStripConnector_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:16.259967+00:00
-- url     : https://prove2.me/theorems/c76bd7d4-fa78-4fa7-a0c7-7131ca310e76
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Strip Connector incidence
-- statement:
--   The vertical Z-corner edge joins precisely the two strip roots of its piece.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L917-L950
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L917-L950

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_incidence
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalStripStripConnector P x S face) target =
      (if target = xLocalRegionRoot P x S face (Sum.inr 0) then 1 else 0) +
        (if target = xLocalRegionRoot P x S face (Sum.inr 1) then 1 else 0) := by sorry
