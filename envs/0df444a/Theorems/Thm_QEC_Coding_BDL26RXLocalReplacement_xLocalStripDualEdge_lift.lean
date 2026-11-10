-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripDualEdge_lift
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:28:51.161194+00:00
-- url     : https://prove2.me/theorems/2f673adb-e96b-4a88-8d3e-05bf58ce84ec
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Dual Edge lift
-- statement:
--   The strip correction lift commutes with the actual X-local coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L658-L666
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L658-L666

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_lift
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalStripDualEdge P x S face side)) =
      (xLocalWordPush (fun i : StripVertex S.half => Sum.inr
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i))).comp
        (graphBoundary (stripStart S.half) (stripEnd S.half)) := by sorry
